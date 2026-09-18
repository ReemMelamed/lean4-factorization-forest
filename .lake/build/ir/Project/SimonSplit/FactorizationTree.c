// Lean compiler output
// Module: Project.SimonSplit.FactorizationTree
// Imports: public import Init public meta import Init public import Mathlib.Data.Fintype.Basic public import Mathlib.Data.Finset.Max public import Project.SimonSplit.Basic public import Project.SimonSplit.Combine public import Project.SimonSplit.Split
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_binary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_binary_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_idempotent_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_idempotent_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_value_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_value_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_listValue_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_listValue_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_Project_SimonSplit_FactorizationTree_ctorIdx___redArg(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx(lean_object* v_A_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lp_Project_SimonSplit_FactorizationTree_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorIdx___boxed(lean_object* v_A_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_Project_SimonSplit_FactorizationTree_ctorIdx(v_A_10_, v_x_11_);
lean_dec_ref(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
if (lean_obj_tag(v_t_13_) == 1)
{
lean_object* v_l_15_; lean_object* v_r_16_; lean_object* v___x_17_; 
v_l_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_l_15_);
v_r_16_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_r_16_);
lean_dec_ref_known(v_t_13_, 2);
v___x_17_ = lean_apply_2(v_k_14_, v_l_15_, v_r_16_);
return v___x_17_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_19_; 
v_a_18_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_18_);
lean_dec_ref(v_t_13_);
v___x_19_ = lean_apply_1(v_k_14_, v_a_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorElim(lean_object* v_A_20_, lean_object* v_motive__1_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_ctorElim___boxed(lean_object* v_A_27_, lean_object* v_motive__1_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_Project_SimonSplit_FactorizationTree_ctorElim(v_A_27_, v_motive__1_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_leaf_elim___redArg(lean_object* v_t_34_, lean_object* v_leaf_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_34_, v_leaf_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_leaf_elim(lean_object* v_A_37_, lean_object* v_motive__1_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_leaf_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_39_, v_leaf_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_binary_elim___redArg(lean_object* v_t_43_, lean_object* v_binary_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_43_, v_binary_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_binary_elim(lean_object* v_A_46_, lean_object* v_motive__1_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_binary_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_48_, v_binary_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_idempotent_elim___redArg(lean_object* v_t_52_, lean_object* v_idempotent_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_52_, v_idempotent_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_idempotent_elim(lean_object* v_A_55_, lean_object* v_motive__1_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_idempotent_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_Project_SimonSplit_FactorizationTree_ctorElim___redArg(v_t_57_, v_idempotent_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value___redArg(lean_object* v_x_61_){
_start:
{
switch(lean_obj_tag(v_x_61_))
{
case 0:
{
lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_a_62_ = lean_ctor_get(v_x_61_, 0);
v___x_63_ = lean_box(0);
lean_inc(v_a_62_);
v___x_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_64_, 0, v_a_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
return v___x_64_;
}
case 1:
{
lean_object* v_l_65_; lean_object* v_r_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_l_65_ = lean_ctor_get(v_x_61_, 0);
v_r_66_ = lean_ctor_get(v_x_61_, 1);
v___x_67_ = lp_Project_SimonSplit_FactorizationTree_value___redArg(v_l_65_);
v___x_68_ = lp_Project_SimonSplit_FactorizationTree_value___redArg(v_r_66_);
v___x_69_ = l_List_appendTR___redArg(v___x_67_, v___x_68_);
return v___x_69_;
}
default: 
{
lean_object* v_children_70_; lean_object* v___x_71_; 
v_children_70_ = lean_ctor_get(v_x_61_, 0);
v___x_71_ = lp_Project_SimonSplit_FactorizationTree_listValue___redArg(v_children_70_);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue___redArg(lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_head_74_ = lean_ctor_get(v_x_72_, 0);
v_tail_75_ = lean_ctor_get(v_x_72_, 1);
v___x_76_ = lp_Project_SimonSplit_FactorizationTree_value___redArg(v_head_74_);
v___x_77_ = lp_Project_SimonSplit_FactorizationTree_listValue___redArg(v_tail_75_);
v___x_78_ = l_List_appendTR___redArg(v___x_76_, v___x_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue___redArg___boxed(lean_object* v_x_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = lp_Project_SimonSplit_FactorizationTree_listValue___redArg(v_x_79_);
lean_dec(v_x_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value___redArg___boxed(lean_object* v_x_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = lp_Project_SimonSplit_FactorizationTree_value___redArg(v_x_81_);
lean_dec_ref(v_x_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value(lean_object* v_A_83_, lean_object* v_x_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_Project_SimonSplit_FactorizationTree_value___redArg(v_x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_value___boxed(lean_object* v_A_86_, lean_object* v_x_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = lp_Project_SimonSplit_FactorizationTree_value(v_A_86_, v_x_87_);
lean_dec_ref(v_x_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue(lean_object* v_A_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lp_Project_SimonSplit_FactorizationTree_listValue___redArg(v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listValue___boxed(lean_object* v_A_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = lp_Project_SimonSplit_FactorizationTree_listValue(v_A_92_, v_x_93_);
lean_dec(v_x_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height___redArg(lean_object* v_x_95_){
_start:
{
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
lean_object* v___x_96_; 
v___x_96_ = lean_unsigned_to_nat(0u);
return v___x_96_;
}
case 1:
{
lean_object* v_l_97_; lean_object* v_r_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_l_97_ = lean_ctor_get(v_x_95_, 0);
v_r_98_ = lean_ctor_get(v_x_95_, 1);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lp_Project_SimonSplit_FactorizationTree_height___redArg(v_l_97_);
v___x_101_ = lp_Project_SimonSplit_FactorizationTree_height___redArg(v_r_98_);
v___x_102_ = lean_nat_dec_le(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec(v___x_101_);
v___x_103_ = lean_nat_add(v___x_99_, v___x_100_);
lean_dec(v___x_100_);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_100_);
v___x_104_ = lean_nat_add(v___x_99_, v___x_101_);
lean_dec(v___x_101_);
return v___x_104_;
}
}
default: 
{
lean_object* v_children_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_children_105_ = lean_ctor_get(v_x_95_, 0);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lp_Project_SimonSplit_FactorizationTree_listHeight___redArg(v_children_105_);
v___x_108_ = lean_nat_add(v___x_106_, v___x_107_);
lean_dec(v___x_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight___redArg(lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_unsigned_to_nat(0u);
return v___x_110_;
}
else
{
lean_object* v_head_111_; lean_object* v_tail_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_head_111_ = lean_ctor_get(v_x_109_, 0);
v_tail_112_ = lean_ctor_get(v_x_109_, 1);
v___x_113_ = lp_Project_SimonSplit_FactorizationTree_height___redArg(v_head_111_);
v___x_114_ = lp_Project_SimonSplit_FactorizationTree_listHeight___redArg(v_tail_112_);
v___x_115_ = lean_nat_dec_le(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_dec(v___x_114_);
return v___x_113_;
}
else
{
lean_dec(v___x_113_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight___redArg___boxed(lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_Project_SimonSplit_FactorizationTree_listHeight___redArg(v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height___redArg___boxed(lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = lp_Project_SimonSplit_FactorizationTree_height___redArg(v_x_118_);
lean_dec_ref(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height(lean_object* v_A_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lp_Project_SimonSplit_FactorizationTree_height___redArg(v_x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_height___boxed(lean_object* v_A_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = lp_Project_SimonSplit_FactorizationTree_height(v_A_123_, v_x_124_);
lean_dec_ref(v_x_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight(lean_object* v_A_126_, lean_object* v_x_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lp_Project_SimonSplit_FactorizationTree_listHeight___redArg(v_x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_FactorizationTree_listHeight___boxed(lean_object* v_A_129_, lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_Project_SimonSplit_FactorizationTree_listHeight(v_A_129_, v_x_130_);
lean_dec(v_x_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_value_match__1_splitter___redArg(lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_, lean_object* v_h__3_135_){
_start:
{
switch(lean_obj_tag(v_x_132_))
{
case 0:
{
lean_object* v_a_136_; lean_object* v___x_137_; 
lean_dec(v_h__3_135_);
lean_dec(v_h__2_134_);
v_a_136_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v_x_132_, 1);
v___x_137_ = lean_apply_1(v_h__1_133_, v_a_136_);
return v___x_137_;
}
case 1:
{
lean_object* v_l_138_; lean_object* v_r_139_; lean_object* v___x_140_; 
lean_dec(v_h__3_135_);
lean_dec(v_h__1_133_);
v_l_138_ = lean_ctor_get(v_x_132_, 0);
lean_inc_ref(v_l_138_);
v_r_139_ = lean_ctor_get(v_x_132_, 1);
lean_inc_ref(v_r_139_);
lean_dec_ref_known(v_x_132_, 2);
v___x_140_ = lean_apply_2(v_h__2_134_, v_l_138_, v_r_139_);
return v___x_140_;
}
default: 
{
lean_object* v_children_141_; lean_object* v___x_142_; 
lean_dec(v_h__2_134_);
lean_dec(v_h__1_133_);
v_children_141_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_children_141_);
lean_dec_ref_known(v_x_132_, 1);
v___x_142_ = lean_apply_1(v_h__3_135_, v_children_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_value_match__1_splitter(lean_object* v_A_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_, lean_object* v_h__3_148_){
_start:
{
switch(lean_obj_tag(v_x_145_))
{
case 0:
{
lean_object* v_a_149_; lean_object* v___x_150_; 
lean_dec(v_h__3_148_);
lean_dec(v_h__2_147_);
v_a_149_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v_x_145_, 1);
v___x_150_ = lean_apply_1(v_h__1_146_, v_a_149_);
return v___x_150_;
}
case 1:
{
lean_object* v_l_151_; lean_object* v_r_152_; lean_object* v___x_153_; 
lean_dec(v_h__3_148_);
lean_dec(v_h__1_146_);
v_l_151_ = lean_ctor_get(v_x_145_, 0);
lean_inc_ref(v_l_151_);
v_r_152_ = lean_ctor_get(v_x_145_, 1);
lean_inc_ref(v_r_152_);
lean_dec_ref_known(v_x_145_, 2);
v___x_153_ = lean_apply_2(v_h__2_147_, v_l_151_, v_r_152_);
return v___x_153_;
}
default: 
{
lean_object* v_children_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_147_);
lean_dec(v_h__1_146_);
v_children_154_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_children_154_);
lean_dec_ref_known(v_x_145_, 1);
v___x_155_ = lean_apply_1(v_h__3_148_, v_children_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_listValue_match__1_splitter___redArg(lean_object* v_x_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_h__2_158_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_1(v_h__1_157_, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v___x_163_; 
lean_dec(v_h__1_157_);
v_head_161_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_head_161_);
v_tail_162_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_tail_162_);
lean_dec_ref_known(v_x_156_, 2);
v___x_163_ = lean_apply_2(v_h__2_158_, v_head_161_, v_tail_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_FactorizationTree_0__SimonSplit_FactorizationTree_listValue_match__1_splitter(lean_object* v_A_164_, lean_object* v_motive_165_, lean_object* v_x_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v_h__2_168_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_apply_1(v_h__1_167_, v___x_169_);
return v___x_170_;
}
else
{
lean_object* v_head_171_; lean_object* v_tail_172_; lean_object* v___x_173_; 
lean_dec(v_h__1_167_);
v_head_171_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_head_171_);
v_tail_172_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_tail_172_);
lean_dec_ref_known(v_x_166_, 2);
v___x_173_ = lean_apply_2(v_h__2_168_, v_head_171_, v_tail_172_);
return v___x_173_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Max(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Basic(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Combine(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Project_Project_SimonSplit_FactorizationTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Max(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Combine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
