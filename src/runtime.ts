/**
 * @file runtime.ts
 *
 * Provides the main runtime functions for interacting with the Emdash system.
 * This includes defining global symbols, adding rewrite and unification rules,
 * and resetting the system's state. These functions orchestrate interactions
 * between state, logic, and elaboration.
 */

import {
    Term, Context, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Icit, Type,
    Hole
} from './types';
import {
    globalDefs, userRewriteRules, userUnificationRules, constraints, emptyCtx,
    freshHoleName, freshVarName, resetVarId, resetHoleId, setDebugVerbose,
    cloneTerm, getTermRef, extendCtx, addConstraint,
    lookupCtx
} from './state';
import { whnf, solveConstraints } from './logic';
import { infer, check } from './elaboration';
import { printTerm, consoleLog } from './utils';


/**
 * Defines a new global symbol (variable or constant) in the system.
 * The type is checked, and if a value is provided, it's checked against the type.
 * @param name Name of the global.
 * @param type Type of the global.
 * @param value Optional definition/value for the global.
 * @param isConstantSymbol True if this is a non-reducible constant symbol.
 * @param isInjective True if this symbol is injective (for unification).
 * @param isTypeNameLike True if this symbol represents a type name that WHNF should not unfold.
 * @param toElaborateType True if the provided type itself should be elaborated and WHNF'd before use.
 */
export function defineGlobal(
    name: string,
    type: Term,
    value?: Term,
    isConstantSymbol: boolean = false,
    isInjective?: boolean,
    isTypeNameLike?: boolean,
    toElaborateType: boolean = false // Typically false, type is assumed elaborated or primitive
) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }

    // Backup and clear constraints for this definition process
    const originalConstraintsBackup = [...constraints];
    constraints.length = 0;

    // Build context from existing global definitions for elaboration
    let elabCtx: Context = emptyCtx;
    globalDefs.forEach(gDef => {
        // Add existing globals to the context for elaborating the new one
        elabCtx = extendCtx(elabCtx, gDef.name, gDef.type, Icit.Expl, gDef.value);
    });

    let elaboratedType: Term;
    let elaboratedValue: Term | undefined = undefined;

    try {
        // Check the provided type against `Type()` to ensure it's a valid type.
        // `toElaborateType` controls if we whnf this elaborated type.
        const checkedType = check(elabCtx, type, Type());
        elaboratedType = toElaborateType ? whnf(getTermRef(checkedType), elabCtx) : checkedType;

        if (value !== undefined) {
            // If a value is provided, check it against the elaborated type.
            // Clone to avoid modifying the original input `value` term during elaboration.
            const valueToCheck = cloneTerm(value); // cloneTerm is currently a no-op
            constraints.length = 0; // Clear constraints specifically for value checking.
            const checkedValueResult = check(elabCtx, valueToCheck, elaboratedType, 0);

            if (!solveConstraints(elabCtx)) {
                const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
                throw new Error(`Global '${name}': Value '${printTerm(value)}' does not type check against declared type '${printTerm(elaboratedType)}'. Unsolved constraints: ${remaining}`);
            }
            elaboratedValue = getTermRef(checkedValueResult); // Use the elaborated and resolved value.
        }

        // Log successful definition.
        let logMessage = `defineGlobal> ${name}`;
        if (isConstantSymbol) logMessage += ' (constant symbol)';
        if (isInjective) logMessage += ' (injective)';
        if (isTypeNameLike) logMessage += ' (type-like)';
        consoleLog(logMessage, {
            type: printTerm(elaboratedType),
            value: elaboratedValue ? printTerm(elaboratedValue) : 'undefined'
        });

        // Store the global definition.
        globalDefs.set(name, { name, type: elaboratedType, value: elaboratedValue, isConstantSymbol, isInjective, isTypeNameLike });

    } catch (e) {
        const error = e as Error;
        console.error(`Failed to define global '${name}': ${error.message}. Stack: ${error.stack}`);
        // Restore constraints to pre-definition state on failure.
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        throw e; // Re-throw the error.
    } finally {
        // Always restore constraints to their state before this defineGlobal call.
        // (Unless an error in value checking left specific constraints we want to expose, handled by the throw).
        // This ensures defineGlobal is somewhat isolated constraint-wise.
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
    }
}

/**
 * Adds a user-defined rewrite rule to the system.
 * The LHS and RHS terms are elaborated to ensure they are well-typed and consistent.
 * @param ruleName Name of the rewrite rule.
 * @param userPatternVars Declared pattern variables (e.g., ["$x", "$A"]).
 * @param rawLhsTerm The Left-Hand Side term of the rule.
 * @param rawRhsTerm The Right-Hand Side term of the rule.
 * @param ctx Context in which the rule is defined (usually emptyCtx for global rules).
 */
export function addRewriteRule(
    ruleName: string,
    userPatternVars: PatternVarDecl[],
    rawLhsTerm: Term,
    rawRhsTerm: Term,
    ctx: Context // Context for elaborating the rule itself.
) {
    const originalConstraintsBackup = [...constraints];
    constraints.length = 0;

    let elaboratedLhs: Term;
    let elaboratedRhs: Term;
    const solvedPatVarTypes = new Map<PatternVarDecl, Term>(); // Store types of pattern vars from LHS.

    try {
        // --- Elaborate LHS ---
        const lhsToElaborate = cloneTerm(rawLhsTerm); // rawLhsTerm might be mutated by infer/check if not cloned.
        let lhsElabCtx: Context = [...ctx]; // Start with the provided context.
        // Extend context with pattern variables, giving them hole types.
        for (const pVarName of userPatternVars) {
            if (!pVarName.startsWith('$')) throw new Error(`Pattern variable ${pVarName} in rule '${ruleName}' must start with '$'.`);
            const pVarHoleType = Hole(freshHoleName() + "_type_pvar_" + pVarName.substring(1));
            (pVarHoleType as Term & {tag:'Hole'}).elaboratedType = Type(); // The hole stands for a type.
            lhsElabCtx = extendCtx(lhsElabCtx, pVarName, pVarHoleType, Icit.Expl);
        }

        // Infer type of LHS to make pattern variables' types concrete.
        infer(lhsElabCtx, lhsToElaborate, 0);

        if (!solveConstraints(lhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' LHS pattern (${printTerm(rawLhsTerm)}) is ill-typed or inconsistent. Unsolved constraints: ${remaining}`);
        }
        elaboratedLhs = getTermRef(lhsToElaborate); // Get the elaborated LHS.

        // Extract solved types for pattern variables from the LHS elaboration context.
        for (const pVarName of userPatternVars) {
            const binding = lookupCtx(lhsElabCtx, pVarName);
            if (binding && binding.type) {
                 solvedPatVarTypes.set(pVarName, getTermRef(binding.type)); // Store whnf'd type.
            } else {
                 // This should not happen if pattern variables were correctly added to context.
                 console.warn(`Pattern variable ${pVarName} not found in LHS elaboration context for rule '${ruleName}'. Assigning fresh hole type.`);
                 solvedPatVarTypes.set(pVarName, Hole(freshHoleName() + "_type_pvar_unfound_" + pVarName.substring(1)));
            }
        }

        // --- Elaborate RHS ---
        const rhsToElaborate = cloneTerm(rawRhsTerm);
        let rhsElabCtx: Context = [...ctx]; // Start with original context for RHS.
        // Extend context with pattern variables using types inferred from LHS.
        for (const pVarName of userPatternVars) {
            const pVarType = solvedPatVarTypes.get(pVarName) || Hole(freshHoleName() + "_type_pvar_rhs_missing_" + pVarName.substring(1));
            rhsElabCtx = extendCtx(rhsElabCtx, pVarName, pVarType, Icit.Expl);
        }

        constraints.length = 0; // Clear constraints for RHS checking.
        // Infer the type of the elaborated LHS in the *global* context (or rule's definition context `ctx`).
        // This gives the target type that the RHS must match.
        const { type: typeOfGlobalLhs } = infer(ctx, elaboratedLhs, 0); // Use `ctx`, not `lhsElabCtx` which has pvars.
         if (!solveConstraints(ctx)) { // Solve any constraints from inferring LHS type in global ctx.
            throw new Error(`Rule '${ruleName}': Could not establish a consistent global type for the elaborated LHS ${printTerm(elaboratedLhs)}.`);
        }
        const targetRhsType = whnf(getTermRef(typeOfGlobalLhs), ctx); // RHS must have this type.

        constraints.length = 0; // Clear for check
        // Check RHS against the type of the LHS.
        check(rhsElabCtx, rhsToElaborate, targetRhsType, 0);

        if (!solveConstraints(rhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' RHS (${printTerm(rawRhsTerm)}) is ill-typed or does not match LHS type (${printTerm(targetRhsType)}). Unsolved constraints: ${remaining}`);
        }
        elaboratedRhs = getTermRef(rhsToElaborate); // Get the elaborated RHS.

        // Add the successfully elaborated rule.
        userRewriteRules.push({ name: ruleName, patternVars: userPatternVars, elaboratedLhs, elaboratedRhs });
        consoleLog(`Rule '${ruleName}' added and elaborated successfully.`,
            `  LHS: ${printTerm(elaboratedLhs)}`,
            `  RHS: ${printTerm(elaboratedRhs)}`
        );

    } catch (e) {
        console.error(`Failed to add rewrite rule '${ruleName}': ${(e as Error).message}. Stack: ${(e as Error).stack}`);
        // Do not add the rule if elaboration failed.
    } finally {
        constraints.splice(0, constraints.length, ...originalConstraintsBackup); // Restore constraints.
    }
}

/**
 * Adds a user-defined unification rule to the system.
 * These rules are used by the `unify` function to guide the unification process.
 * @param rule The unification rule to add.
 */
export function addUnificationRule(rule: UnificationRule) {
    // TODO: Potentially elaborate unification rule patterns similar to rewrite rules for consistency?
    // For now, they are added as-is. The `matchPattern` used by `tryUnificationRules`
    // will operate on these raw patterns. Elaboration could ensure well-formedness.
    userUnificationRules.push(rule);
    consoleLog(`Unification rule '${rule.name}' added.`);
}

/**
 * Resets the entire Emdash system state to its initial empty state.
 * Clears global definitions, rules, constraints, and resets ID counters.
 */
export function resetMyLambdaPi() {
    constraints.length = 0;
    globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    resetVarId();
    resetHoleId();
    setDebugVerbose(false); // Default to non-verbose.
    consoleLog("Emdash system state reset.");
}