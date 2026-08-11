// Lean compiler output
// Module: Project.FactorizationForest.Basic
// Imports: public import Init public meta import Init public import Mathlib.Data.Fintype.Card public import Mathlib.Data.Finset.Max public import Project.GreensRelations.Order
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___closed__0 = (const lean_object*)&lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_binary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_binary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_nary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_nary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_list__to__nary___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_list__to__nary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_list__to__nary_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_list__to__nary_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_FactorizationTree_word_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_FactorizationTree_word_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___redArg___lam__0(lean_object* v_u_3_, lean_object* v_eval_4_, lean_object* v_i_5_, lean_object* v_j_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = lean_nat_sub(v_j_6_, v_i_5_);
v___x_8_ = l_List_drop___redArg(v_i_5_, v_u_3_);
v___x_9_ = ((lean_object*)(lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___closed__0));
lean_inc(v___x_8_);
v___x_10_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v___x_8_, v___x_8_, v___x_7_, v___x_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_apply_1(v_eval_4_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___boxed(lean_object* v_u_12_, lean_object* v_eval_13_, lean_object* v_i_14_, lean_object* v_j_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_Project_FactorizationForest_wordLabeling___redArg___lam__0(v_u_12_, v_eval_13_, v_i_14_, v_j_15_);
lean_dec(v_j_15_);
lean_dec(v_u_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___redArg(lean_object* v_eval_17_, lean_object* v_u_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_19_, 0, v_u_18_);
lean_closure_set(v___f_19_, 1, v_eval_17_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling(lean_object* v_A_20_, lean_object* v_S_21_, lean_object* v_inst_22_, lean_object* v_eval_23_, lean_object* v_hmul_24_, lean_object* v_u_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = lean_alloc_closure((void*)(lp_Project_FactorizationForest_wordLabeling___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_26_, 0, v_u_25_);
lean_closure_set(v___f_26_, 1, v_eval_23_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_wordLabeling___boxed(lean_object* v_A_27_, lean_object* v_S_28_, lean_object* v_inst_29_, lean_object* v_eval_30_, lean_object* v_hmul_31_, lean_object* v_u_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_Project_FactorizationForest_wordLabeling(v_A_27_, v_S_28_, v_inst_29_, v_eval_30_, v_hmul_31_, v_u_32_);
lean_dec(v_inst_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx___redArg(lean_object* v_x_34_){
_start:
{
switch(lean_obj_tag(v_x_34_))
{
case 0:
{
lean_object* v___x_35_; 
v___x_35_ = lean_unsigned_to_nat(0u);
return v___x_35_;
}
case 1:
{
lean_object* v___x_36_; 
v___x_36_ = lean_unsigned_to_nat(1u);
return v___x_36_;
}
default: 
{
lean_object* v___x_37_; 
v___x_37_ = lean_unsigned_to_nat(2u);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx___redArg___boxed(lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = lp_Project_FactorizationForest_FactorizationTree_ctorIdx___redArg(v_x_38_);
lean_dec_ref(v_x_38_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx(lean_object* v_A_40_, lean_object* v_x_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_Project_FactorizationForest_FactorizationTree_ctorIdx___redArg(v_x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorIdx___boxed(lean_object* v_A_43_, lean_object* v_x_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_Project_FactorizationForest_FactorizationTree_ctorIdx(v_A_43_, v_x_44_);
lean_dec_ref(v_x_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(lean_object* v_t_46_, lean_object* v_k_47_){
_start:
{
switch(lean_obj_tag(v_t_46_))
{
case 0:
{
lean_object* v_a_48_; lean_object* v___x_49_; 
v_a_48_ = lean_ctor_get(v_t_46_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v_t_46_, 1);
v___x_49_ = lean_apply_1(v_k_47_, v_a_48_);
return v___x_49_;
}
case 1:
{
lean_object* v_left_50_; lean_object* v_right_51_; lean_object* v_word_52_; lean_object* v_height_53_; lean_object* v___x_54_; 
v_left_50_ = lean_ctor_get(v_t_46_, 0);
lean_inc_ref(v_left_50_);
v_right_51_ = lean_ctor_get(v_t_46_, 1);
lean_inc_ref(v_right_51_);
v_word_52_ = lean_ctor_get(v_t_46_, 2);
lean_inc(v_word_52_);
v_height_53_ = lean_ctor_get(v_t_46_, 3);
lean_inc(v_height_53_);
lean_dec_ref_known(v_t_46_, 4);
v___x_54_ = lean_apply_4(v_k_47_, v_left_50_, v_right_51_, v_word_52_, v_height_53_);
return v___x_54_;
}
default: 
{
lean_object* v_children_55_; lean_object* v_word_56_; lean_object* v_height_57_; lean_object* v___x_58_; 
v_children_55_ = lean_ctor_get(v_t_46_, 0);
lean_inc(v_children_55_);
v_word_56_ = lean_ctor_get(v_t_46_, 1);
lean_inc(v_word_56_);
v_height_57_ = lean_ctor_get(v_t_46_, 2);
lean_inc(v_height_57_);
lean_dec_ref_known(v_t_46_, 3);
v___x_58_ = lean_apply_3(v_k_47_, v_children_55_, v_word_56_, v_height_57_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorElim(lean_object* v_A_59_, lean_object* v_motive__1_60_, lean_object* v_ctorIdx_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_k_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_62_, v_k_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_ctorElim___boxed(lean_object* v_A_66_, lean_object* v_motive__1_67_, lean_object* v_ctorIdx_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_k_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim(v_A_66_, v_motive__1_67_, v_ctorIdx_68_, v_t_69_, v_h_70_, v_k_71_);
lean_dec(v_ctorIdx_68_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_leaf_elim___redArg(lean_object* v_t_73_, lean_object* v_leaf_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_73_, v_leaf_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_leaf_elim(lean_object* v_A_76_, lean_object* v_motive__1_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_leaf_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_78_, v_leaf_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_binary_elim___redArg(lean_object* v_t_82_, lean_object* v_binary_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_82_, v_binary_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_binary_elim(lean_object* v_A_85_, lean_object* v_motive__1_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_binary_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_87_, v_binary_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_nary_elim___redArg(lean_object* v_t_91_, lean_object* v_nary_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_91_, v_nary_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_nary_elim(lean_object* v_A_94_, lean_object* v_motive__1_95_, lean_object* v_t_96_, lean_object* v_h_97_, lean_object* v_nary_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lp_Project_FactorizationForest_FactorizationTree_ctorElim___redArg(v_t_96_, v_nary_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word___redArg(lean_object* v_x_100_){
_start:
{
switch(lean_obj_tag(v_x_100_))
{
case 0:
{
lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_a_101_ = lean_ctor_get(v_x_100_, 0);
v___x_102_ = lean_box(0);
lean_inc(v_a_101_);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v_a_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
return v___x_103_;
}
case 1:
{
lean_object* v_word_104_; 
v_word_104_ = lean_ctor_get(v_x_100_, 2);
lean_inc(v_word_104_);
return v_word_104_;
}
default: 
{
lean_object* v_word_105_; 
v_word_105_ = lean_ctor_get(v_x_100_, 1);
lean_inc(v_word_105_);
return v_word_105_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word___redArg___boxed(lean_object* v_x_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lp_Project_FactorizationForest_FactorizationTree_word___redArg(v_x_106_);
lean_dec_ref(v_x_106_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word(lean_object* v_A_108_, lean_object* v_x_109_){
_start:
{
switch(lean_obj_tag(v_x_109_))
{
case 0:
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v_x_109_, 0);
v___x_111_ = lean_box(0);
lean_inc(v_a_110_);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v_a_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
case 1:
{
lean_object* v_word_113_; 
v_word_113_ = lean_ctor_get(v_x_109_, 2);
lean_inc(v_word_113_);
return v_word_113_;
}
default: 
{
lean_object* v_word_114_; 
v_word_114_ = lean_ctor_get(v_x_109_, 1);
lean_inc(v_word_114_);
return v_word_114_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_word___boxed(lean_object* v_A_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_Project_FactorizationForest_FactorizationTree_word(v_A_115_, v_x_116_);
lean_dec_ref(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height___redArg(lean_object* v_x_118_){
_start:
{
switch(lean_obj_tag(v_x_118_))
{
case 0:
{
lean_object* v___x_119_; 
v___x_119_ = lean_unsigned_to_nat(0u);
return v___x_119_;
}
case 1:
{
lean_object* v_height_120_; 
v_height_120_ = lean_ctor_get(v_x_118_, 3);
lean_inc(v_height_120_);
return v_height_120_;
}
default: 
{
lean_object* v_height_121_; 
v_height_121_ = lean_ctor_get(v_x_118_, 2);
lean_inc(v_height_121_);
return v_height_121_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height___redArg___boxed(lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = lp_Project_FactorizationForest_FactorizationTree_height___redArg(v_x_122_);
lean_dec_ref(v_x_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height(lean_object* v_A_124_, lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lp_Project_FactorizationForest_FactorizationTree_height___redArg(v_x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_FactorizationTree_height___boxed(lean_object* v_A_127_, lean_object* v_x_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = lp_Project_FactorizationForest_FactorizationTree_height(v_A_127_, v_x_128_);
lean_dec_ref(v_x_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_list__to__nary___redArg(lean_object* v_children_130_, lean_object* v_u_131_, lean_object* v_h_132_, lean_object* v_def__leaf_133_){
_start:
{
if (lean_obj_tag(v_children_130_) == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_h_132_);
v___x_134_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_def__leaf_133_);
v___x_135_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_135_, 0, v_def__leaf_133_);
lean_ctor_set(v___x_135_, 1, v_def__leaf_133_);
lean_ctor_set(v___x_135_, 2, v_u_131_);
lean_ctor_set(v___x_135_, 3, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v_tail_136_; 
lean_dec_ref(v_def__leaf_133_);
v_tail_136_ = lean_ctor_get(v_children_130_, 1);
if (lean_obj_tag(v_tail_136_) == 0)
{
lean_object* v_head_137_; lean_object* v___x_138_; 
v_head_137_ = lean_ctor_get(v_children_130_, 0);
lean_inc_n(v_head_137_, 2);
lean_dec_ref_known(v_children_130_, 2);
v___x_138_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_138_, 0, v_head_137_);
lean_ctor_set(v___x_138_, 1, v_head_137_);
lean_ctor_set(v___x_138_, 2, v_u_131_);
lean_ctor_set(v___x_138_, 3, v_h_132_);
return v___x_138_;
}
else
{
lean_object* v_tail_139_; 
v_tail_139_ = lean_ctor_get(v_tail_136_, 1);
if (lean_obj_tag(v_tail_139_) == 0)
{
lean_object* v_head_140_; lean_object* v_head_141_; lean_object* v___x_142_; 
lean_inc_ref(v_tail_136_);
v_head_140_ = lean_ctor_get(v_children_130_, 0);
lean_inc(v_head_140_);
lean_dec_ref_known(v_children_130_, 2);
v_head_141_ = lean_ctor_get(v_tail_136_, 0);
lean_inc(v_head_141_);
lean_dec_ref_known(v_tail_136_, 2);
v___x_142_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_142_, 0, v_head_140_);
lean_ctor_set(v___x_142_, 1, v_head_141_);
lean_ctor_set(v___x_142_, 2, v_u_131_);
lean_ctor_set(v___x_142_, 3, v_h_132_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_143_, 0, v_children_130_);
lean_ctor_set(v___x_143_, 1, v_u_131_);
lean_ctor_set(v___x_143_, 2, v_h_132_);
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_FactorizationForest_list__to__nary(lean_object* v_A_144_, lean_object* v_children_145_, lean_object* v_u_146_, lean_object* v_h_147_, lean_object* v_def__leaf_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lp_Project_FactorizationForest_list__to__nary___redArg(v_children_145_, v_u_146_, v_h_147_, v_def__leaf_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_list__to__nary_match__1_splitter___redArg(lean_object* v_children_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_, lean_object* v_h__4_154_){
_start:
{
if (lean_obj_tag(v_children_150_) == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_h__4_154_);
lean_dec(v_h__3_153_);
lean_dec(v_h__2_152_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_apply_1(v_h__1_151_, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_tail_157_; 
lean_dec(v_h__1_151_);
v_tail_157_ = lean_ctor_get(v_children_150_, 1);
if (lean_obj_tag(v_tail_157_) == 0)
{
lean_object* v_head_158_; lean_object* v___x_159_; 
lean_dec(v_h__4_154_);
lean_dec(v_h__3_153_);
v_head_158_ = lean_ctor_get(v_children_150_, 0);
lean_inc(v_head_158_);
lean_dec_ref_known(v_children_150_, 2);
v___x_159_ = lean_apply_1(v_h__2_152_, v_head_158_);
return v___x_159_;
}
else
{
lean_object* v_tail_160_; 
lean_inc_ref(v_tail_157_);
lean_dec(v_h__2_152_);
v_tail_160_ = lean_ctor_get(v_tail_157_, 1);
if (lean_obj_tag(v_tail_160_) == 0)
{
lean_object* v_head_161_; lean_object* v_head_162_; lean_object* v___x_163_; 
lean_dec(v_h__4_154_);
v_head_161_ = lean_ctor_get(v_children_150_, 0);
lean_inc(v_head_161_);
lean_dec_ref_known(v_children_150_, 2);
v_head_162_ = lean_ctor_get(v_tail_157_, 0);
lean_inc(v_head_162_);
lean_dec_ref_known(v_tail_157_, 2);
v___x_163_ = lean_apply_2(v_h__3_153_, v_head_161_, v_head_162_);
return v___x_163_;
}
else
{
lean_object* v_head_164_; lean_object* v_head_165_; lean_object* v_head_166_; lean_object* v_tail_167_; lean_object* v___x_168_; 
lean_inc_ref(v_tail_160_);
lean_dec(v_h__3_153_);
v_head_164_ = lean_ctor_get(v_children_150_, 0);
lean_inc(v_head_164_);
lean_dec_ref_known(v_children_150_, 2);
v_head_165_ = lean_ctor_get(v_tail_157_, 0);
lean_inc(v_head_165_);
lean_dec_ref_known(v_tail_157_, 2);
v_head_166_ = lean_ctor_get(v_tail_160_, 0);
lean_inc(v_head_166_);
v_tail_167_ = lean_ctor_get(v_tail_160_, 1);
lean_inc(v_tail_167_);
lean_dec_ref_known(v_tail_160_, 2);
v___x_168_ = lean_apply_4(v_h__4_154_, v_head_164_, v_head_165_, v_head_166_, v_tail_167_);
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_list__to__nary_match__1_splitter(lean_object* v_A_169_, lean_object* v_motive_170_, lean_object* v_children_171_, lean_object* v_h__1_172_, lean_object* v_h__2_173_, lean_object* v_h__3_174_, lean_object* v_h__4_175_){
_start:
{
if (lean_obj_tag(v_children_171_) == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_h__4_175_);
lean_dec(v_h__3_174_);
lean_dec(v_h__2_173_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_1(v_h__1_172_, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v_tail_178_; 
lean_dec(v_h__1_172_);
v_tail_178_ = lean_ctor_get(v_children_171_, 1);
if (lean_obj_tag(v_tail_178_) == 0)
{
lean_object* v_head_179_; lean_object* v___x_180_; 
lean_dec(v_h__4_175_);
lean_dec(v_h__3_174_);
v_head_179_ = lean_ctor_get(v_children_171_, 0);
lean_inc(v_head_179_);
lean_dec_ref_known(v_children_171_, 2);
v___x_180_ = lean_apply_1(v_h__2_173_, v_head_179_);
return v___x_180_;
}
else
{
lean_object* v_tail_181_; 
lean_inc_ref(v_tail_178_);
lean_dec(v_h__2_173_);
v_tail_181_ = lean_ctor_get(v_tail_178_, 1);
if (lean_obj_tag(v_tail_181_) == 0)
{
lean_object* v_head_182_; lean_object* v_head_183_; lean_object* v___x_184_; 
lean_dec(v_h__4_175_);
v_head_182_ = lean_ctor_get(v_children_171_, 0);
lean_inc(v_head_182_);
lean_dec_ref_known(v_children_171_, 2);
v_head_183_ = lean_ctor_get(v_tail_178_, 0);
lean_inc(v_head_183_);
lean_dec_ref_known(v_tail_178_, 2);
v___x_184_ = lean_apply_2(v_h__3_174_, v_head_182_, v_head_183_);
return v___x_184_;
}
else
{
lean_object* v_head_185_; lean_object* v_head_186_; lean_object* v_head_187_; lean_object* v_tail_188_; lean_object* v___x_189_; 
lean_inc_ref(v_tail_181_);
lean_dec(v_h__3_174_);
v_head_185_ = lean_ctor_get(v_children_171_, 0);
lean_inc(v_head_185_);
lean_dec_ref_known(v_children_171_, 2);
v_head_186_ = lean_ctor_get(v_tail_178_, 0);
lean_inc(v_head_186_);
lean_dec_ref_known(v_tail_178_, 2);
v_head_187_ = lean_ctor_get(v_tail_181_, 0);
lean_inc(v_head_187_);
v_tail_188_ = lean_ctor_get(v_tail_181_, 1);
lean_inc(v_tail_188_);
lean_dec_ref_known(v_tail_181_, 2);
v___x_189_ = lean_apply_4(v_h__4_175_, v_head_185_, v_head_186_, v_head_187_, v_tail_188_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_FactorizationTree_word_match__1_splitter___redArg(lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_, lean_object* v_h__3_193_){
_start:
{
switch(lean_obj_tag(v_x_190_))
{
case 0:
{
lean_object* v_a_194_; lean_object* v___x_195_; 
lean_dec(v_h__3_193_);
lean_dec(v_h__2_192_);
v_a_194_ = lean_ctor_get(v_x_190_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v_x_190_, 1);
v___x_195_ = lean_apply_1(v_h__1_191_, v_a_194_);
return v___x_195_;
}
case 1:
{
lean_object* v_left_196_; lean_object* v_right_197_; lean_object* v_word_198_; lean_object* v_height_199_; lean_object* v___x_200_; 
lean_dec(v_h__3_193_);
lean_dec(v_h__1_191_);
v_left_196_ = lean_ctor_get(v_x_190_, 0);
lean_inc_ref(v_left_196_);
v_right_197_ = lean_ctor_get(v_x_190_, 1);
lean_inc_ref(v_right_197_);
v_word_198_ = lean_ctor_get(v_x_190_, 2);
lean_inc(v_word_198_);
v_height_199_ = lean_ctor_get(v_x_190_, 3);
lean_inc(v_height_199_);
lean_dec_ref_known(v_x_190_, 4);
v___x_200_ = lean_apply_4(v_h__2_192_, v_left_196_, v_right_197_, v_word_198_, v_height_199_);
return v___x_200_;
}
default: 
{
lean_object* v_children_201_; lean_object* v_word_202_; lean_object* v_height_203_; lean_object* v___x_204_; 
lean_dec(v_h__2_192_);
lean_dec(v_h__1_191_);
v_children_201_ = lean_ctor_get(v_x_190_, 0);
lean_inc(v_children_201_);
v_word_202_ = lean_ctor_get(v_x_190_, 1);
lean_inc(v_word_202_);
v_height_203_ = lean_ctor_get(v_x_190_, 2);
lean_inc(v_height_203_);
lean_dec_ref_known(v_x_190_, 3);
v___x_204_ = lean_apply_3(v_h__3_193_, v_children_201_, v_word_202_, v_height_203_);
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_FactorizationForest_Basic_0__FactorizationForest_FactorizationTree_word_match__1_splitter(lean_object* v_A_205_, lean_object* v_motive_206_, lean_object* v_x_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_, lean_object* v_h__3_210_){
_start:
{
switch(lean_obj_tag(v_x_207_))
{
case 0:
{
lean_object* v_a_211_; lean_object* v___x_212_; 
lean_dec(v_h__3_210_);
lean_dec(v_h__2_209_);
v_a_211_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v_x_207_, 1);
v___x_212_ = lean_apply_1(v_h__1_208_, v_a_211_);
return v___x_212_;
}
case 1:
{
lean_object* v_left_213_; lean_object* v_right_214_; lean_object* v_word_215_; lean_object* v_height_216_; lean_object* v___x_217_; 
lean_dec(v_h__3_210_);
lean_dec(v_h__1_208_);
v_left_213_ = lean_ctor_get(v_x_207_, 0);
lean_inc_ref(v_left_213_);
v_right_214_ = lean_ctor_get(v_x_207_, 1);
lean_inc_ref(v_right_214_);
v_word_215_ = lean_ctor_get(v_x_207_, 2);
lean_inc(v_word_215_);
v_height_216_ = lean_ctor_get(v_x_207_, 3);
lean_inc(v_height_216_);
lean_dec_ref_known(v_x_207_, 4);
v___x_217_ = lean_apply_4(v_h__2_209_, v_left_213_, v_right_214_, v_word_215_, v_height_216_);
return v___x_217_;
}
default: 
{
lean_object* v_children_218_; lean_object* v_word_219_; lean_object* v_height_220_; lean_object* v___x_221_; 
lean_dec(v_h__2_209_);
lean_dec(v_h__1_208_);
v_children_218_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_children_218_);
v_word_219_ = lean_ctor_get(v_x_207_, 1);
lean_inc(v_word_219_);
v_height_220_ = lean_ctor_get(v_x_207_, 2);
lean_inc(v_height_220_);
lean_dec_ref_known(v_x_207_, 3);
v___x_221_ = lean_apply_3(v_h__3_210_, v_children_218_, v_word_219_, v_height_220_);
return v___x_221_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Max(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Project_Project_FactorizationForest_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Card(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Max(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_GreensRelations_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
