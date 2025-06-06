import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole,
    FMap0Term, FMap1Term, NatTransComponentTerm, CatTerm, ObjTerm, HomTerm, FunctorTypeTerm, SetTerm, NatTransTypeTerm
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, FH
} from '../src/state';
import { defineGlobal } from '../src/globals';
import { resetMyLambdaPi_Emdash } from '../src/stdlib';
import { areEqual } from '../src/equality';
import { elaborate, check } from '../src/elaboration';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';

describe("Kernel Implicit Argument Tests", () => {
    let ctx: Context;
    let CatA: Term, CatB: Term, CatC: Term;
    let ObjX_A: Term, ObjY_A: Term, ObjZ_A: Term;
    let FunctorF_AB: Term, FunctorG_AB: Term, FunctorH_BC: Term;
    let Morph_a_XY: Term;
    let Transf_eps_FG: Term;

    beforeEach(() => {
        resetMyLambdaPi_Emdash();
        ctx = emptyCtx;

        // Define Categories
        defineGlobal("CatA", CatTerm());
        defineGlobal("CatB", CatTerm());
        defineGlobal("CatC", CatTerm());
        CatA = Var("CatA");
        CatB = Var("CatB");
        CatC = Var("CatC");

        // Define Objects
        defineGlobal("ObjX_A", ObjTerm(CatA));
        defineGlobal("ObjY_A", ObjTerm(CatA));
        defineGlobal("ObjZ_A", ObjTerm(CatA));
        ObjX_A = Var("ObjX_A");
        ObjY_A = Var("ObjY_A");
        ObjZ_A = Var("ObjZ_A");

        // Define Functors
        defineGlobal("FunctorF_AB", FunctorTypeTerm(CatA, CatB));
        defineGlobal("FunctorG_AB", FunctorTypeTerm(CatA, CatB));
        defineGlobal("FunctorH_BC", FunctorTypeTerm(CatB, CatC));
        FunctorF_AB = Var("FunctorF_AB");
        FunctorG_AB = Var("FunctorG_AB");
        FunctorH_BC = Var("FunctorH_BC");

        // Define Morphism
        defineGlobal("Morph_a_XY", HomTerm(CatA, ObjX_A, ObjY_A));
        Morph_a_XY = Var("Morph_a_XY");
        
        // Define Natural Transformation
        defineGlobal("Transf_eps_FG", NatTransTypeTerm(CatA, CatB, FunctorF_AB, FunctorG_AB));
        Transf_eps_FG = Var("Transf_eps_FG");
    });

    it("Test 1: FMap0Term should have implicit categories inserted", () => {
        // Construct FMap0Term without explicit implicit args
        const rawFmap0 = FMap0Term(FunctorF_AB, ObjX_A);
        
        // The expected type of the functor is Functor CatA CatB
        // The expected type of the object is Obj CatA
        // The expected result type is Obj CatB

        const result = elaborate(rawFmap0);
        
        const expectedType = ObjTerm(CatB);
        assert(areEqual(result.type, expectedType, ctx), `Test 1: Elaborated type should be Obj CatB, but got ${printTerm(result.type)}`);

        // Check if the elaborated term has the implicits filled
        const elaboratedTerm = getTermRef(result.term) as Term & { tag: 'FMap0Term' };
        assert(elaboratedTerm.tag === 'FMap0Term', "Test 1: Elaborated term should be FMap0Term");
        assert(elaboratedTerm.catA_IMPLICIT !== undefined, "Test 1: catA_IMPLICIT should be inserted");
        assert(elaboratedTerm.catB_IMPLICIT !== undefined, "Test 1: catB_IMPLICIT should be inserted");

        // The inserted implicits should be unified with the correct categories
        assert(areEqual(getTermRef(elaboratedTerm.catA_IMPLICIT!), CatA, ctx), "Test 1: Inserted catA should be CatA");
        assert(areEqual(getTermRef(elaboratedTerm.catB_IMPLICIT!), CatB, ctx), "Test 1: Inserted catB should be CatB");
    });

    it("Test 2: FMap1Term should have all implicits inserted", () => {
        // fmap1 F a
        const rawFmap1 = FMap1Term(FunctorF_AB, Morph_a_XY);

        const result = elaborate(rawFmap1);
        
        // Expected result type: Hom CatB (fmap0 F X) (fmap0 F Y)
        const fmap0_F_X = FMap0Term(FunctorF_AB, ObjX_A, CatA, CatB);
        const fmap0_F_Y = FMap0Term(FunctorF_AB, ObjY_A, CatA, CatB);
        const expectedType = HomTerm(CatB, fmap0_F_X, fmap0_F_Y);

        assert(areEqual(result.type, expectedType, ctx), `Test 2: Elaborated type mismatch. Got ${printTerm(result.type)}`);
        
        const elaboratedTerm = getTermRef(result.term) as Term & { tag: 'FMap1Term' };
        assert(elaboratedTerm.tag === 'FMap1Term', "Test 2: Elaborated term should be FMap1Term");
        assert(elaboratedTerm.catA_IMPLICIT !== undefined, "Test 2: catA_IMPLICIT should be inserted");
        assert(elaboratedTerm.catB_IMPLICIT !== undefined, "Test 2: catB_IMPLICIT should be inserted");
        assert(elaboratedTerm.objX_A_IMPLICIT !== undefined, "Test 2: objX_A_IMPLICIT should be inserted");
        assert(elaboratedTerm.objY_A_IMPLICIT !== undefined, "Test 2: objY_A_IMPLICIT should be inserted");

        assert(areEqual(getTermRef(elaboratedTerm.catA_IMPLICIT!), CatA, ctx), "Test 2: catA check failed");
        assert(areEqual(getTermRef(elaboratedTerm.catB_IMPLICIT!), CatB, ctx), "Test 2: catB check failed");
        assert(areEqual(getTermRef(elaboratedTerm.objX_A_IMPLICIT!), ObjX_A, ctx), "Test 2: objX_A check failed");
        assert(areEqual(getTermRef(elaboratedTerm.objY_A_IMPLICIT!), ObjY_A, ctx), "Test 2: objY_A check failed");
    });
    
    it("Test 3: NatTransComponentTerm (tapp) should have implicits inserted", () => {
        // tapp eps X
        const rawTapp = NatTransComponentTerm(Transf_eps_FG, ObjX_A);

        const result = elaborate(rawTapp);

        // Expected result type: Hom CatB (fmap0 F X) (fmap0 G X)
        const fmap0_F_X = FMap0Term(FunctorF_AB, ObjX_A, CatA, CatB);
        const fmap0_G_X = FMap0Term(FunctorG_AB, ObjX_A, CatA, CatB);
        const expectedType = HomTerm(CatB, fmap0_F_X, fmap0_G_X);

        assert(areEqual(result.type, expectedType, ctx), `Test 3: Elaborated type mismatch. Got ${printTerm(result.type)}`);

        const elaboratedTerm = getTermRef(result.term) as Term & { tag: 'NatTransComponentTerm' };
        assert(elaboratedTerm.tag === 'NatTransComponentTerm', "Test 3: Elaborated term should be NatTransComponentTerm");
        assert(elaboratedTerm.catA_IMPLICIT !== undefined, "Test 3: catA_IMPLICIT should be inserted");
        assert(elaboratedTerm.catB_IMPLICIT !== undefined, "Test 3: catB_IMPLICIT should be inserted");
        assert(elaboratedTerm.functorF_IMPLICIT !== undefined, "Test 3: functorF_IMPLICIT should be inserted");
        assert(elaboratedTerm.functorG_IMPLICIT !== undefined, "Test 3: functorG_IMPLICIT should be inserted");

        assert(areEqual(getTermRef(elaboratedTerm.catA_IMPLICIT!), CatA, ctx), "Test 3: catA check failed");
        assert(areEqual(getTermRef(elaboratedTerm.catB_IMPLICIT!), CatB, ctx), "Test 3: catB check failed");
        assert(areEqual(getTermRef(elaboratedTerm.functorF_IMPLICIT!), FunctorF_AB, ctx), "Test 3: functorF check failed");
        assert(areEqual(getTermRef(elaboratedTerm.functorG_IMPLICIT!), FunctorG_AB, ctx), "Test 3: functorG check failed");
    });

    it("Test 4: Elaboration should fail if implicits clash", () => {
        // fmap0 F X, but we tell it the functor is from A->C, while F is A->B
        const rawFmap0 = FMap0Term(FunctorF_AB, ObjX_A, undefined, CatC); // Provide wrong catB

        try {
            elaborate(rawFmap0);
            assert(false, "Test 4: Elaboration should have failed due to clashing implicit info");
        } catch (e) {
            const err = e as Error;
            // The error should be a constraint failure, as it tries to unify FunctorType(A,B) with FunctorType(A,C)
            assert(err.message.includes("Could not solve constraints"), `Test 4: Expected constraint error, but got: ${err.message}`);
        }
    });
}); 