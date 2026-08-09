/**
 * Curated browser-safe authoring entry for direct TypeScript/emdash work.
 *
 * Authoring constructs ordinary explicit Core and outer-LF artifacts. Class
 * schemas, providers, instance synthesis, and call elaboration erase to those
 * checked terms; they add no class node or declaration text parser to Core.
 */

export * from './package_core';
export * from './lf';
export * from './lf_builder';
export * from './lf_checker';
export * from './lf_conversion';
export * from './lf_declarations';
export * from './lf_transfer';
export * from './lf_transfer_compiler';
export * from './lf_transfer_runtime';
export * from './lf_transfer_mixed';
export * from './lf_transfer_visibility';
export * from './lf_transfer_proof';
export * from './lf_structure_macro';
export * from './lf_adjunction_macro';
export * from './lf_dictionary_synthesis';
export * from './lf_dictionary_authoring';
export * from './lf_class_schema';
export * from './lf_class_inheritance';
export * from './lf_class_inheritance_lowering';
export * from './lf_instance_scope';
export * from './lf_instance_synthesis';
export * from './lf_class_call_elaboration';
