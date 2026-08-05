/**
 * Checked SCALE-STRESS-3B acquisition for the protected hom-action closure
 * and the proof-heavy equality-evidence theorem closure.
 *
 * This is exact source/export evidence only. It parses no term, installs no
 * declaration, and grants no theorem body or product computation policy.
 */

import {
    CoreLfCanonicalCommandExpectation,
    CoreLfCanonicalSelectionContract,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition_contract';

type SymbolExpectationTuple = readonly [
    ordinal: number,
    name: string,
    textSha256: string,
    isProtected: boolean
];

const symbolExpectations = (
    prefix: string,
    tuples: readonly SymbolExpectationTuple[]
): readonly CoreLfCanonicalCommandExpectation[] =>
    tuples.map(([
        ordinal,
        name,
        textSha256,
        isProtected
    ]) => ({
        id: `${prefix}.${name}`,
        ordinal,
        kind: 'symbol' as const,
        textSha256,
        name,
        modifiers: isProtected
            ? ['protected'] as const
            : [] as const,
        hasBody: true
    }));

const PROTECTED_HOM_ACTION_CLOSURE = [
    [1, 'eq1_left_functor', 'sha256:476a40a15395b2802b27aa1aa63fb40269e349b565f1d8644ef35b4bfe2990f6', true],
    [2, 'eq1_right_functor', 'sha256:f1b296d33daefb67f5a322d7da88b251107c54c0ec2b62bbe68243c4490227ed', true],
    [3, 'eq1_left_to_transf', 'sha256:634e90a12209b2b2b6a5bcfb7628d9e30753ebb9ba771086b399d0c75c599882', true],
    [4, 'eq1_left_from_transf', 'sha256:a9eac3574b98c27a8be2170cc1140521f0f5437bc4c2564bc300c1fd40c2e0a7', true],
    [5, 'eq1_left_to_component', 'sha256:f6503e95fc976eae65957efbd62380569c47fc0fd58f20ce6ce4bc2e7b55c9bd', true],
    [6, 'eq1_left_from_component', 'sha256:020955bcadc510baa0f8fafa12fac8b839059454cc04bfc7f00b382f0d0a19e5', true],
    [7, 'eq1_fapp1_left_inv', 'sha256:71ce606be9b812e19e56c4ee9456ae9052aec9932ce9d04bd5d2854dd0506122', true],
    [8, 'eq1_left_right_functor_path', 'sha256:f5b8d3baa95469d30760438eb37304796206021fc203c6aed4e62895ec4c5074', true],
    [9, 'eq1_left_functor_right_law', 'sha256:d20312a503612a0f8a643a5cd83b6b57660921626ad2cb9d1ce2901f0738ed36', true],
    [10, 'eq1_functor_path_component', 'sha256:13f6b66153588c5d84d16905bf17fb9b41bc4a91a1ad8f6a512f185f569b9751', true],
    [11, 'eq1_eq_ap_trans', 'sha256:6e23d3dc29c5b1e96cbd4999887ea0594fdbc80227f19e04b7e2ebe2f374ec21', true],
    [12, 'eq1_eq_ap_sym', 'sha256:395537c1888a5b509979b4c1205a59d778b0c32fae5a934e209e35c8a7993ff9', true],
    [13, 'eq1_left_path_component', 'sha256:7363a68c12608be20c068c4b948cf038b256984535a0a3d2c61026f8877ef630', true],
    [14, 'eq1_left_right_path_component', 'sha256:5e4b22897f3b576f7459b29ed3d93416fdf94df9d0e47f38a29b6d85da15455c', true],
    [15, 'eq1_adjusted_right_component_path', 'sha256:5d25497c25695e278bf6068135d53791fc355d76998b226a0a07e9dea7459455', true],
    [16, 'eq1_triangle_forward_path', 'sha256:a12ac680f4976d63153081ef3e0107d57a8055aa825324d421cce102de503fb6', true],
    [17, 'eq1_half_adjoint_triangle_point', 'sha256:cd508a0cac73903c30e053dc8bc8ea754965e67c48d02c4b30b7bdbda81815be', true],
    [18, 'eq1_adjusted_right_stage1_path', 'sha256:4291aec49515f226613e68c78b05952807e25a39f94dd5d405505f40c58b58d9', true],
    [19, 'eq1_adjusted_right_stage2_path', 'sha256:4124ac69299e358c52407fb39a9819aa2006aae1c92f25d1ca31eab8d1c79a0f', true],
    [20, 'eq1_adjusted_right_law_factored', 'sha256:2a826b268b20dcdbf637e898b9693ae44650251729720fd2c11574a88568906e', true],
    [21, 'eq1_adjusted_stage1_component', 'sha256:bf495aaba0b3e189c4d50dc3e38b2ebb586b360e891920aeebe4108b6ef3074e', true],
    [22, 'eq1_adjusted_stage2_component', 'sha256:c90f74369a55979c07347286c8169bb8e1084eeb18ab657a8f136df8ea60d6e1', true],
    [23, 'eq1_adjusted_stage1_component_agrees', 'sha256:6ade061c6c484404e0a962589ec5a69053e90ce3f72275328eaa7979f1b699f6', true],
    [24, 'eq1_adjusted_stage2_component_agrees', 'sha256:3a4c66f2844b6d718101f3dc1bb59fdc58ab286d9e721914edd198a75a938ffb', true],
    [25, 'eq1_adjusted_component_raw', 'sha256:6a34be5e99f503a21fc8ad7357bd064843521fc85983d168a91c01cc3614ae0c', true],
    [26, 'eq1_functor_path_component_trans', 'sha256:884a1c4ef7cc9a2dc5091df8d38a4b5332831db3001d09895e99118e29d4f499', true],
    [27, 'eq1_adjusted_component_agrees', 'sha256:fdd781b037c0564aee8c85d82fc107e53d791901cad50cd14f06e94b64f78873', true],
    [28, 'eq1_path_to_component', 'sha256:b68b4eb441481428e09b8ce4baf500a3e22087cf40977454650b5007fed79299', true],
    [29, 'eq1_path_from_component', 'sha256:fb7856c9ed5cd6e5b8b571033c0f960524e1d3b1b49b666e45a2aa27a3de90fc', true],
    [30, 'eq1_path_to_component_agrees', 'sha256:05622a253c1cf9e596e3dbba51057021733d8c0d73456ef20504fb14277ade74', true],
    [31, 'eq1_path_from_component_eq_sym_agrees', 'sha256:e06fb099a79bbafa000edb4233249840bca8ce8b0389c251b099f27229acca2a', true],
    [32, 'eq1_path_to_hom_fapp1_agrees', 'sha256:d03952d48bde2225cb2490e7ff01aa795a83465dcacd200739c850885b89c945', true],
    [33, 'eq1_triangle_forward_hom_agrees', 'sha256:de461ef4b260db0056a877149d22e6968532d17c2e1ee25295e4a8e1a72f43bb', true],
    [34, 'eq1_adjusted_to_hom_agrees', 'sha256:98f5fbb73cb9b98667b7a92a8a5a481315005d30532c76801d4dba98fa6bedae', true],
    [35, 'eq1_half_adjoint_triangle_hom', 'sha256:9f8a8b124d684f754bcdc6c1e5f4b6749738a05a256a71acd9812f449c0dc287', true],
    [36, 'eq1_half_adjoint_triangle_to_component', 'sha256:e168103638378deebff259ffd731d77d655413e9d924ac542aeaba7ccdcd81f4', true],
    [37, 'eq1_half_adjoint_triangle_raw', 'sha256:3cbbfd70cf17074d5b30b5278059d4c1b3935b6b43dac7da5a9083e606cd6adc', true],
    [38, 'eq1_half_adjoint_triangle_reverse_path', 'sha256:87f03c35b325df3b3f4a7ab585094513e189f8720f2474bdbe666041976edac1', true],
    [39, 'eq1_triangle_reverse_hom_agrees', 'sha256:5e7202b31eeee1b376595a0e76631a7a40872690711262a8032c57c036c6e20f', true],
    [40, 'eq1_half_adjoint_triangle_from_component', 'sha256:a41c1867e82ea133328f9f59f61f7b8921f4b1ff50bf40d87a85c30562882579', true],
    [41, 'eq1_path_conjugate_hom', 'sha256:b40a499a9760c73f8f5a9b2040d8893848cde0d18ed10ff6ea20ade230ce5fc2', true],
    [42, 'eq1_path_conjugate_hom_law', 'sha256:af3aeae10024e4d0cab2dc84b5f28d3b32ef636e73e7ca64d5ae8b23676d8370', true],
    [43, 'eq1_fapp1_left_right_conjugate_raw', 'sha256:c77fd66a315e330b82f584c7bd8a7348d300586402e785886d94f61649a85f86', true],
    [44, 'eq1_functor_path_Hom_fapp1_naturality', 'sha256:21d2a4865bd0c482083fc6e043bdd8704997e74e4b1b351a497328f1834e0b3e', true],
    [45, 'eq1_fapp1_left_right_naturality_middle', 'sha256:c189c235736571562ccb06470a60beaba9559cf1274762d9cba7ba67e6363f33', true],
    [46, 'eq1_fapp1_left_right_conjugate_middle', 'sha256:eb637b0a0cabf45721a30a92e34b1786da176548922e78959ace6f37b15c5bce', true],
    [47, 'eq1_fapp1_left_right_assoc_step', 'sha256:dcb3a626b180611fc0f84b8319c10205f5213be54390b6ed7d32b9c2aef229aa', true],
    [48, 'eq1_fapp1_left_right_naturality_step', 'sha256:acb47a35117c4ef8af56ad3f2af6114c33aaef2b6b2597fa46685d1a3b587cb5', true],
    [49, 'eq1_fapp1_left_right_raw_assoc_step', 'sha256:c65a6a9c0e9836b06754f48a7542686c30f29c5ecc19b5fb71652796836167a2', true],
    [50, 'eq1_fapp1_left_right_raw_path', 'sha256:9e999dbb82f3ad45ee792851a9c401310105a097234eba29bad19523410c82ad', true],
    [51, 'eq1_adjusted_Hom_func_actual', 'sha256:2c27baee1b5e42b9e66a1548628a8f309c6aeeb7044e373e14ea73846c949bbc', true],
    [52, 'eq1_adjusted_Hom_func_source_replaced', 'sha256:b595c347cb2672fb766cdcfd4faf8338419fc2fd5af7bf2c93aa386f93f0c5d1', true],
    [53, 'eq1_adjusted_Hom_func_path', 'sha256:e7d3907c36d8ecdebfb55aa58341c6436a5b060667d9592286a4cfc31a9a6189', true],
    [54, 'eq1_fapp1_left_right_raw_adjusted_path', 'sha256:c09159e2dc8cdd8eb397ab28fe94fc48b68a942c8468aa8c2344c265ec1d570d', true],
    [55, 'eq1_fapp1_left_right_law', 'sha256:ead8e1c5731b68a4475517be23d49fa7032f14dfc0d6a3d6be2dfe79592e20d9', true],
    [56, 'eq1_fapp1_left_left_law', 'sha256:af51ca929b1a60f890ecf53c1f2451eedcbc1ee51a8cab2044b557aea812de5f', true],
    [58, 'omega_equiv_along_fapp1', 'sha256:65035d42a79957970101219fab3077070aeade22adcbae7897ff1aec8f4fbd65', false],
    [59, 'groupoidal_core_homwise', 'sha256:9f164499bcb66561c8dc20bc1e4e0ed8b5957b3843cc1db56683886f055ee184', false]
] as const satisfies readonly SymbolExpectationTuple[];

const EVIDENCE_PROPERTY_CLOSURE = [
    [2, 'OmegaEquivLeftView', 'sha256:acb92e19b503a3fa02b4bd6c5622675353476035c97645d2d28cd5a2764a770b', false],
    [3, 'OmegaEquivRightView', 'sha256:801c56cae556e32d2cce0bee5401dd23990b0fba12f533354baae4ea4e68a621', false],
    [4, 'OmegaEquivAlongView', 'sha256:3a8cf3437550334c1ccb7a08e0c96c0948f196aaf4be7ae6173638059332328a', false],
    [5, 'omega_equiv_along_view', 'sha256:508296a9cc5a90c61477714c9a6bfa82ea0555774763c2951e14b2e6f8a3bc14', false],
    [6, 'omega_equiv_along_from_view', 'sha256:8b7b0e095bb1c8615624e6eed099008fbe99a6f1cc867a0a5b500de3ee86a2d0', false],
    [7, 'omega_equiv_along_from_view_view', 'sha256:71933d2a9ee88ca2ad3c414bc9e7f672e8b43271e4a6066922488b06e1c1e5d9', false],
    [8, 'omega_equiv_along_view_is_contr', 'sha256:c275992ba7645e513d0e23642545eca371a060a4a7e968d5aad2dfac044af8d7', false],
    [9, 'omega_equiv_along_evidence_is_contr_from_view', 'sha256:44ac2a42688208e1d9d7a195776f94554adb6c4950e543affaf79cf954676a41', false],
    [28, 'omega_equiv_candidate_left_to_right', 'sha256:51a65b12c531eb462fa4a7b1340233865da27e79221256606acc07e0678e71c5', false],
    [38, 'omega_equiv_right_as_left_law', 'sha256:c80204de02db8c890de720f706d6e6bb0238c80f0e9ee02ff0d909508fe6be34', false],
    [39, 'omega_equiv_left_as_right_law', 'sha256:7cf628bd227b3f099f638a7749552a3eef861fa18093d4cbb58b424ec58e2882', false],
    [40, 'omega_equiv_left_comp_map', 'sha256:e5d8048bbce0e00163214ac99acf08dc9d938b6a48b2fb1e240a8fc3ce37505e', false],
    [41, 'omega_equiv_left_comp_inverse', 'sha256:5fd8cecdeafa82138a7f6d8b9ea866904d5895ef45998806e0d376dd7682ecc3', false],
    [42, 'omega_equiv_left_comp_eta', 'sha256:a760dbf2dc5b20500da5cbd712e2a6f03214b1aea6957a7e8967b2d576870618', false],
    [43, 'omega_equiv_left_comp_epsilon', 'sha256:a801e93906421676be5022df09c796c9b4a68cbb618ce7f39bca9a92cb5faaa1', false],
    [44, 'omega_equiv_left_comp_by_inverse', 'sha256:4774ce3b3a6deeb72eb7657a3f669d042ef44d9df2070345325d4ab0d150efeb', false],
    [45, 'omega_equiv_left_view_is_contr', 'sha256:8e13e63474c8822302b4af6966ba6a91cb04269a621a5974d40f6f4ecd71de34', false],
    [46, 'omega_equiv_right_comp_map', 'sha256:6d0dcdf011db702ae5d9b7f5299c7dff0daacebc45aa54d9315467a5a29f1328', false],
    [47, 'omega_equiv_right_comp_inverse', 'sha256:9eac05b74f1074423eb0905e3853f4a3629f9c3cc88f6c00789180a63b615603', false],
    [48, 'omega_equiv_right_comp_eta', 'sha256:7549bb56486a41165eb3cb8ccfa54ec8df2294484455b244ec116656083a29e4', false],
    [49, 'omega_equiv_right_comp_epsilon', 'sha256:4878f5b37a3ff9effe39333299a25cf93d3bb9955d2231f882a3bda6bf3ce3a8', false],
    [50, 'omega_equiv_right_comp_by_inverse', 'sha256:145aa087da04d66d3284db979041fedb994cc2a0a81de8b61b20373876a65890', false],
    [51, 'omega_equiv_right_view_is_contr', 'sha256:b6ca071d342ff65d0fa51886e2d61d6377eef563c50e42821e73fafce3cc308e', false],
    [52, 'omega_equiv_along_evidence_is_contr', 'sha256:3f892f1a75c5705200504f6e19866906561a19f000059f26659b7ea53132a540', false],
    [53, 'omega_equiv_along_evidence_is_prop', 'sha256:5c5e1089e0824af5dda8c9e4070ec359d58f3b26bfe0a1a43d43c0e74df8a9b8', false]
] as const satisfies readonly SymbolExpectationTuple[];

export const CORE_LF_SCALE_STRESS_3B_PROTECTED_HOM_ACTION_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision:
            'SCALE-STRESS-3B-PROTECTED-HOM-ACTION-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2_eq1_hom_action',
        authorityPath:
            'emdash2/emdash3_2_eq1_hom_action.lp',
        sourceSha256:
            'sha256:e5ff82d49d26d60fa20f28cc3eea5915c70a0379768076912f617d4ae5da5356',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:000dd93e025ebb9e6efe2621fa74257a2ffe547107f353f590c31088aa9b0be0',
            imports: ['emdash.emdash3_2']
        },
        commands: symbolExpectations(
            'protected-hom-action',
            PROTECTED_HOM_ACTION_CLOSURE
        )
    });

export const CORE_LF_SCALE_STRESS_3B_EVIDENCE_PROPERTY_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision:
            'SCALE-STRESS-3B-EVIDENCE-PROPERTY-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2_eq1_evidence_property',
        authorityPath:
            'emdash2/emdash3_2_eq1_evidence_property.lp',
        sourceSha256:
            'sha256:7d93a91d0cfb38e80905fd6f5e29a061b2888b04815999ca9d4a309d8811619c',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:83075b38429baee5b03c7829b2d82f908a04b374cdb839249a54dda72835f4ee',
            imports: [
                'emdash.emdash3_2',
                'emdash.emdash3_2_eq1_hom_action'
            ]
        },
        commands: symbolExpectations(
            'evidence-property',
            EVIDENCE_PROPERTY_CLOSURE
        )
    });

/**
 * Measured audit facts used to choose the next typed-acquisition tranche.
 * Byte counts cover only the selected canonical symbol commands.
 */
export const CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT =
    Object.freeze({
        revision: 'SCALE-STRESS-3B-ACQUISITION-AUDIT-1',
        protectedHomAction: Object.freeze({
            target: 'groupoidal_core_homwise',
            commandCount: 58,
            protectedCommandCount: 56,
            explicitTermCommandCount: 56,
            tacticCommandCount: 2,
            canonicalCommandBytes: 63_945,
            tacticSymbols: Object.freeze([
                'eq1_adjusted_component_agrees',
                'eq1_fapp1_left_right_law'
            ]),
            ordinals: Object.freeze(
                PROTECTED_HOM_ACTION_CLOSURE.map(entry => entry[0])
            )
        }),
        evidenceProperty: Object.freeze({
            target: 'omega_equiv_along_evidence_is_prop',
            commandCount: 25,
            protectedCommandCount: 0,
            explicitTermCommandCount: 25,
            tacticCommandCount: 0,
            canonicalCommandBytes: 14_614,
            ordinals: Object.freeze(
                EVIDENCE_PROPERTY_CLOSURE.map(entry => entry[0])
            )
        }),
        rootPrerequisite: Object.freeze({
            directlyReferencedNameCount: 57,
            sourcePriorCommandCount: 90,
            consumerAvailableCommandCount: 20,
            partiallyAvailableInductiveCommands: Object.freeze([
                'τΣ_'
            ]),
            missingCommandCount: 70,
            missingSymbolCommandCount: 68,
            missingInductiveCommandCount: 2,
            missingExplicitTermCommandCount: 49,
            missingAbsentBodyCommandCount: 19,
            missingCanonicalCommandBytes: 24_131,
            missingInductiveCommands: Object.freeze([
                'TruncLevel',
                'OmegaEquivAlongEqData'
            ])
        }),
        semanticStatus: 'checked-acquisition-only',
        nextBoundary:
            'SCALE-ACQUIRE-1B canonical symbol declaration adapter, then ' +
            'an explicit root prerequisite/generated-owner boundary'
    });
