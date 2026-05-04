# ICMS 2026 Session 1 Abstract (Draft)

**Title:** MathOps for Automating Reasoning in Strict/Lax ω-Categories: emdash2 in Lambdapi

https://github.com/hotdocx/emdash

We present **emdash2**, a Lambdapi development for strict/lax ω-categories aimed at automating mathematical reasoning through typed rewriting and higher-order unification. The core idea is to encode symbolic categorical algorithms directly as computational rules in the proof-assistant kernel: functor action, transformation components, naturality accumulation, exchange-style rewrites, and draft adjunction triangle cut-elimination. This gives an algebraic specification and formal semantics where many coherence obligations are discharged by normalization during type checking.

The project is developed in a **MathOps** workflow that links three layers: (1) a proof assistant kernel (Lambdapi) for trusted checking, (2) a strict diagrammatic JSON language (Arrowgram) for commutative-diagram specifications, and (3) a generative AI coding loop that proposes definitions/rules from diagrammatic intent. Candidate code is accepted only after kernel verification, creating a practical LLM ↔ proof-checker feedback loop.

From the ICMS session perspective, emdash2 contributes a concrete bridge between interactive theorem proving, symbolic computation, and AI-assisted formalization. The same rewrite-head discipline that supports higher-categorical proofs also provides a path toward CAS integration: symbolic transformations can be imported as typed, checkable rewrite interfaces instead of opaque external steps.
