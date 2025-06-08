/**
 * @file globals.ts
 * @description Provides functions for managing global definitions,
 * user-defined rewrite rules, and user-defined unification rules.
 * These functions interact with the global state and use the elaboration
 * and logic modules to process and validate definitions and rules.
 */

import {
    Term, Context, GlobalDef, PatternVarDecl, UnificationRule, Icit,
    Type, Hole
} from './types';
import {
    globalDefs, userRewriteRules, userUnificationRules, constraints, emptyCtx,
    freshHoleName,
    getTermRef, extendCtx, consoleLog, printTerm, lookupCtx
} from './state';
import { whnf } from './reduction';
import { solveConstraints } from './unification';
import { areEqual } from './equality';
import { infer, check } from './elaboration';

/**
 * Defines a new global symbol.
 * @param name The name of the global symbol.
 * @param type The type of the global symbol.
 * @param value Optional definition/value for the symbol.
 * @param isConstantSymbol True if the symbol is a primitive constant (affects rewriting and unfolding).
 * @param isInjective True if the symbol is an injective constructor (for unification).
 * @param toElaborateType True if the provided type itself needs to be elaborated and checked against Type.
 */
export function defineGlobal(
    name: string,
    type: Term,
    value?: Term,
    isConstantSymbol: boolean = false,
    isInjective?: boolean,
    toElaborateType: boolean = false // If true, `type` is elaborated; otherwise, it's taken as already valid.
) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }

    const originalConstraintsBackup = [...constraints];
    constraints.length = 0; // Clear constraints for this definition

    // Build a context from existing global definitions for elaboration
    let elabCtx: Context = emptyCtx;
    globalDefs.forEach(gDef => {
        // Only add non-dependent globals to this simple context construction.
        // A more sophisticated approach might be needed for inter-dependent global types.
        elabCtx = extendCtx(elabCtx, gDef.name, gDef.type, Icit.Expl, gDef.value);
    });

    let elaboratedType: Term;
    let elaboratedValue: Term | undefined = undefined;

    try {
        elaboratedType = check(elabCtx, type, Type());
        elaboratedType = toElaborateType ? whnf(getTermRef(elaboratedType), elabCtx) : whnf(getTermRef(type), elabCtx);

        if (value !== undefined) {
            const valueToCheck = value
            constraints.length = 0; // Fresh constraints for checking the value
            const checkedValueResult = check(elabCtx, valueToCheck, elaboratedType, 0);

            if (!solveConstraints(elabCtx)) {
                const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
                throw new Error(`Global '${name}': Value '${printTerm(value)}' does not type check against declared type '${printTerm(elaboratedType)}'. Unsolved constraints: ${remaining}`);
            }
            elaboratedValue = getTermRef(checkedValueResult); // Store the elaborated and dereferenced value
        }

        console.log('defineGlobal> ', { name: name + (isConstantSymbol ? ' (constant symbol)' : '')
            + (isInjective ? ' (injective)' : ''),
            type: printTerm(elaboratedType), value: elaboratedValue ? printTerm(elaboratedValue) : 'undefined' });

        globalDefs.set(name, { name, type: elaboratedType, value: elaboratedValue, isConstantSymbol, isInjective });

    } catch (e) {
        const error = e as Error;
        console.error(`Failed to define global '${name}': ${error.message}. Stack: ${error.stack}`);
        constraints.splice(0, constraints.length, ...originalConstraintsBackup); // Restore original constraints on failure
        throw e; // Re-throw the error
    } finally {
        // Ensure original constraints are restored if this function didn't throw but a sub-call did and was caught internally.
        if (constraints.length !== originalConstraintsBackup.length || !constraints.every((c, i) => c === originalConstraintsBackup[i])) {
             constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        }
    }
}

/**
 * Adds a new user-defined rewrite rule.
 * The LHS and RHS terms are elaborated before storage.
 * @param ruleName The name of the rewrite rule.
 * @param userPatternVars An array of pattern variable names (e.g., ["$x", "$y"]).
 * @param rawLhsTerm The raw left-hand side term of the rule.
 * @param rawRhsTerm The raw right-hand side term of the rule.
 * @param ctx The context in which the rule is defined (usually emptyCtx for global rules).
 */
export function addRewriteRule(
    ruleName: string,
    userPatternVars: PatternVarDecl[],
    rawLhsTerm: Term,
    rawRhsTerm: Term,
    ctx: Context // Context for elaborating the rule, typically emptyCtx
) {
    const originalConstraintsBackup = [...constraints];
    constraints.length = 0; // Clear constraints for this rule addition

    let elaboratedLhs: Term;
    let elaboratedRhs: Term;
    const solvedPatVarTypes = new Map<PatternVarDecl, Term>(); // To store types of pattern variables

    try {
        // --- Elaborate LHS ---
        const lhsToElaborate = rawLhsTerm;
        let lhsElabCtx: Context = [...ctx]; // Start with the provided context
        // Extend context with pattern variables, typed by holes
        for (const pVarName of userPatternVars) {
            if (!pVarName.startsWith('$')) throw new Error(`Pattern variable ${pVarName} in rule '${ruleName}' must start with '$'.`);
            // Assign a fresh hole as the type for each pattern variable for inference
            lhsElabCtx = extendCtx(lhsElabCtx, pVarName, Hole(freshHoleName() + "_type_pvar_" + pVarName.substring(1)), Icit.Expl);
        }

        const elabOptions = { skipCoherenceCheck: true, patternMode: true };

        // Infer the types within the LHS and solve for pattern variable types
        infer(lhsElabCtx, lhsToElaborate, 0, elabOptions); // This will generate constraints

        if (!solveConstraints(lhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' LHS pattern (${printTerm(rawLhsTerm)}) is ill-typed or inconsistent. Unsolved constraints: ${remaining}`);
        }
        elaboratedLhs = getTermRef(lhsToElaborate); // Store the elaborated LHS

        // Retrieve the solved types for pattern variables from the elaboration context
        for (const pVarName of userPatternVars) {
            const binding = lookupCtx(lhsElabCtx, pVarName);
            if (binding && binding.type) { // Type should always be present after extendCtx
                 solvedPatVarTypes.set(pVarName, getTermRef(binding.type)); // Store dereferenced type
            } else {
                 // This case should ideally not be reached if pattern vars are correctly added to context.
                 console.warn(`Pattern variable ${pVarName} not found in LHS elaboration context for rule '${ruleName}'. Assigning a fresh hole type.`);
                 solvedPatVarTypes.set(pVarName, Hole(freshHoleName() + "_type_pvar_unfound_" + pVarName.substring(1)));
            }
        }

        // --- Elaborate RHS ---
        const rhsToElaborate = rawRhsTerm;
        let rhsElabCtx: Context = [...ctx]; // Start with the provided context again
        // Extend context with pattern variables, now using their solved types from LHS elaboration
        for (const pVarName of userPatternVars) {
            const pVarType = solvedPatVarTypes.get(pVarName) || Hole(freshHoleName() + "_type_pvar_rhs_missing_" + pVarName.substring(1));
            rhsElabCtx = extendCtx(rhsElabCtx, pVarName, pVarType, Icit.Expl);
        }

        constraints.length = 0; // Fresh constraints for RHS
        // Infer the type of the elaborated LHS in the *global* context (or rule's definition context)
        // to determine the target type for the RHS.
        const typeOfGlobalLhsResult = infer(lhsElabCtx, elaboratedLhs, 0, elabOptions); // Use lhsElabCtx, not original ctx
         if (!solveConstraints(ctx)) { // Solve constraints that arose from inferring type of elaboratedLhs
            throw new Error(`Rule '${ruleName}': Could not establish a consistent global type for the elaborated LHS ${printTerm(elaboratedLhs)}.`);
        }
        const targetRhsType = whnf(getTermRef(typeOfGlobalLhsResult.type), ctx); // Target type for RHS

        constraints.length = 0; // Fresh constraints for checking RHS against target type
        // Check the RHS against this target type
        console.log("rhsElabCtx>>>", rhsElabCtx.map(b => `${b.name}: ${printTerm(b.type)}`).join('; '));
        check(rhsElabCtx, rhsToElaborate, targetRhsType, 0);

        if (!solveConstraints(rhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' RHS (${printTerm(rawRhsTerm)}) is ill-typed or does not match LHS type (${printTerm(targetRhsType)}). Unsolved constraints: ${remaining}`);
        }
        elaboratedRhs = getTermRef(rhsToElaborate); // Store the elaborated RHS

        // Add the fully elaborated rule
        userRewriteRules.push({ name: ruleName, patternVars: userPatternVars, elaboratedLhs, elaboratedRhs });
        console.log(`Rule '${ruleName}' added and elaborated successfully.`,
            `LHS: ${printTerm(elaboratedLhs)}`,
            `RHS: ${printTerm(elaboratedRhs)}`
        );

    } catch (e) {
        console.error(`Failed to add rewrite rule '${ruleName}': ${(e as Error).message}. Stack: ${(e as Error).stack}`);
        // Restore constraints on failure
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        // Do not re-throw here, to allow other definitions/rules to proceed. Or, decide to make it fatal.
    } finally {
        // Ensure original constraints are restored if this function didn't throw but a sub-call did
        if (constraints.length !== originalConstraintsBackup.length || !constraints.every((c, i) => c === originalConstraintsBackup[i])) {
            constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        }
    }
}

/**
 * Adds a new user-defined unification rule.
 * These rules are used by the `unify` function to guide the unification process.
 * @param rule The unification rule to add.
 */
export function addUnificationRule(rule: UnificationRule) {
    // TODO: Consider elaborating patterns in unification rules similar to rewrite rules
    // for type consistency and resolving pattern variable types.
    // For now, they are added as is.
    userUnificationRules.push(rule);
    console.log(`Unification rule '${rule.name}' added.`);
}