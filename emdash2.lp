/*
  m— / emdash2
  Functorial programming for (strict/lax) ω-categories in Lambdapi.
*/

// ===== START OF BASIC KERNEL (MVP) =====

flag "eta_equality" on;

// A minimal “Type : TYPE” + decoding function `τ : Type → TYPE`,
// mirroring the setup in `emdash.lp` so we can internalize “sets of terms”.
constant symbol Type : TYPE;
injective symbol τ : Type → TYPE;
builtin "T" ≔ τ;
builtin "Prop" ≔ Type;
builtin "P" ≔ τ;

// A tiny inhabited type, useful for “always-true” unification-rule conditions.
inductive unit : TYPE ≔ | tt : unit;

// Minimal naturals (dimension index).
inductive Nat : TYPE ≔
| Z : Nat
| S : Nat → Nat;

// ===== END OF BASIC KERNEL (MVP) =====

// ===== START OF ω-CATEGORY INFRASTRUCTURE (SKELETON) =====

// NOTE: This is intentionally skeletal: the goal is to keep the file compiling
// while we incrementally add the real globular/stratified typing discipline.

constant symbol OCat : TYPE;

// n-cells of an ω-category C.
constant symbol Cell : OCat → Nat → TYPE;

// Source/target of (n+1)-cells landing in n-cells.
symbol src : Π [C : OCat] (n : Nat), Cell C (S n) → Cell C n;
symbol tgt : Π [C : OCat] (n : Nat), Cell C (S n) → Cell C n;

// Placeholder “identity raising” operation (will be refined).
symbol id : Π [C : OCat] (n : Nat), Cell C n → Cell C (S n);

// ===== END OF ω-CATEGORY INFRASTRUCTURE (SKELETON) =====
