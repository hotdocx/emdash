// src/macros.ts
import createMacro, { MacroError } from 'ts-macros';
import * as ts from 'typescript';
import { parseToSyntaxTree } from './parser-logic';
import { Term, Icit } from './types'; // Import types for type-safety within the macro

export const term = createMacro(function term(ctx) {
    // 1. Extract the string from the tagged template literal
    const source = ctx.node.template.rawText;
    if (source === undefined) {
        throw new MacroError(ctx.node, "Macro must be used as a tagged template literal.");
    }

    // 2. Parse the string into our intermediate syntactic Term representation
    let parsedTerm: Term;
    try {
        parsedTerm = parseToSyntaxTree(source);
    } catch (e: any) {
        throw new MacroError(ctx.node, `Failed to parse term: ${e.message}`);
    }
    
    // 3. Ensure necessary runtime functions and enums are imported
    const { factory } = ctx;
    // These utils must be imported in the file where the macro is called.
    // `ctx.addUtil` handles this automatically.
    const Var = ctx.addUtil('Var', './types');
    const Lam = ctx.addUtil('Lam', './types');
    const App = ctx.addUtil('App', './types');
    const Pi = ctx.addUtil('Pi', './types');
    const Type = ctx.addUtil('Type', './types');
    const IcitEnum = ctx.addUtil('Icit', './types');
    const replaceFreeVar = ctx.addUtil('replaceFreeVar', './pattern');

    // Helper to get the AST for an Icit enum member
    const getIcitAST = (icit: Icit) => factory.createPropertyAccessExpression(
        IcitEnum,
        icit === Icit.Expl ? 'Expl' : 'Impl'
    );

    // 4. Recursively convert the parsed Term object into a TypeScript AST
    function termToAST(term: Term): ts.Expression {
        switch (term.tag) {
            case 'Var':
                return factory.createCallExpression(Var, undefined, [factory.createStringLiteral(term.name)]);
            case 'Type':
                return factory.createCallExpression(Type, undefined, []);
            case 'App':
                return factory.createCallExpression(App, undefined, [
                    termToAST(term.func),
                    termToAST(term.arg),
                    getIcitAST(term.icit)
                ]);
            case 'Lam': {
                const paramName = term.paramName;
                const paramVar = factory.createIdentifier("v"); // The name for the lambda parameter, e.g., `(v) => ...`
                
                // The body from the parser is a simple function returning the body term
                const bodyTerm = term.body(Var('_dummy_')); 
                const bodyAST = termToAST(bodyTerm);
                
                const hoasBody = factory.createArrowFunction(
                    undefined, undefined,
                    [factory.createParameterDeclaration(undefined, undefined, paramVar)],
                    undefined,
                    factory.createToken(ts.SyntaxKind.EqualsGreaterThanToken),
                    // The body of our HOAS function is a call to `replaceFreeVar`
                    factory.createCallExpression(replaceFreeVar, undefined, [
                        bodyAST,
                        factory.createStringLiteral(paramName),
                        paramVar
                    ])
                );

                const paramTypeAST = term.paramType ? termToAST(term.paramType) : factory.createIdentifier('undefined');
                const isAnnotatedAST = term.paramType ? factory.createTrue() : factory.createFalse();
                
                // Reconstruct Lam(name, icit, type, body, isAnnotated)
                // We need to adjust the Lam constructor to accept this form or have a different one.
                // Let's assume Lam can be called as `Lam(name, icit, type_or_body, body_or_nothing)`
                return factory.createCallExpression(Lam, undefined, [
                    factory.createStringLiteral(paramName),
                    getIcitAST(term.icit),
                    paramTypeAST,
                    hoasBody
                ]);
            }
            case 'Pi': {
                const paramName = term.paramName;
                const paramVar = factory.createIdentifier("v");
                const bodyTypeTerm = term.bodyType(Var('_dummy_'));
                const bodyTypeAST = termToAST(bodyTypeTerm);

                const hoasBodyType = factory.createArrowFunction(
                    undefined, undefined,
                    [factory.createParameterDeclaration(undefined, undefined, paramVar)],
                    undefined,
                    factory.createToken(ts.SyntaxKind.EqualsGreaterThanToken),
                    factory.createCallExpression(replaceFreeVar, undefined, [
                        bodyTypeAST,
                        factory.createStringLiteral(paramName),
                        paramVar
                    ])
                );
                
                return factory.createCallExpression(Pi, undefined, [
                    factory.createStringLiteral(paramName),
                    getIcitAST(term.icit),
                    termToAST(term.paramType),
                    hoasBodyType
                ]);
            }
            default:
                throw new MacroError(ctx.node, `AST generation not implemented for term tag: ${term.tag}`);
        }
    }
    
    // 5. Replace the macro call with the generated AST
    ctx.node.replace(termToAST(parsedTerm));
});