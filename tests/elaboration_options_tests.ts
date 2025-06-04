/**
 * @file tests/elaboration_options_tests.ts
 * @description Tests for elaboration options, like `normalizeResultTerm`.
 */
import {
    Term, Icit, Type, Lam, App
} from '../src/types';
import {
    emptyCtx, printTerm
} from '../src/state';
import {
    resetMyLambdaPi_Emdash
} from '../src/stdlib';
import {
    elaborate, ElaborationOptions
} from '../src/elaboration';
import { assertEqual, assert } from './utils';

import { describe, it } from 'node:test'; // Added for node:test
import { resetMyLambdaPi } from '../src/core_context_globals';

describe("Elaboration Options Tests", () => {

    it("Test 1: Elaborate with normalizeResultTerm:false", () => {
        resetMyLambdaPi();
        const ctx = emptyCtx;
        const termRaw = App(Lam("x", Icit.Expl, Type(), (x_var: Term): Term => x_var), Type(), Icit.Expl);
        const elabOpts: ElaborationOptions = { normalizeResultTerm: false };
        const elabRes = elaborate(termRaw, undefined, ctx, elabOpts);

        assert(elabRes.term.tag === 'App', "ElabNoNorm.1: Result term should be App (not normalized)");
        if (elabRes.term.tag === 'App') {
            assert(elabRes.term.func.tag === 'Lam', "ElabNoNorm.1: Function part of App should be Lam");
            assert(elabRes.term.arg.tag === 'Type', "ElabNoNorm.1: Argument part of App should be Type");
        }
        assertEqual(printTerm(elabRes.type), "Type", "ElabNoNorm.1: Type (which is always normalized) should be Type");
        console.log("Test Elaborate with normalizeResultTerm:false Passed.");
    });
});