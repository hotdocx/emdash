import { Context, Binding, Term } from './types';
import { globalDefs, userRewriteRules, userUnificationRules, constraints, nextVarId, nextHoleId, DEBUG_VERBOSE } from './globals_and_rules';

export const emptyCtx: Context = [];
export const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (DEBUG_VERBOSE) {
        console.log(message, ...optionalParams);
    }
}

export function resetMyLambdaPi() {
    // @ts-ignore implicit any
    constraints.length = 0; // Clear array by setting length to 0
    globalDefs.clear();
    // @ts-ignore implicit any
    userRewriteRules.length = 0;
    // @ts-ignore implicit any
    userUnificationRules.length = 0;
    // @ts-ignore implicit any
    nextVarId = 0;
    // @ts-ignore implicit any
    nextHoleId = 0;
} 