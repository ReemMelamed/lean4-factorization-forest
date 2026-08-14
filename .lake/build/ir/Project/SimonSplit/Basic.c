// Lean compiler output
// Module: Project.SimonSplit.Basic
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
static const lean_array_object lp_Project_SimonSplit_wordLabeling___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_Project_SimonSplit_wordLabeling___redArg___lam__0___closed__0 = (const lean_object*)&lp_Project_SimonSplit_wordLabeling___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___redArg___lam__0(lean_object* v_u_3_, lean_object* v_eval_4_, lean_object* v_i_5_, lean_object* v_j_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = lean_nat_sub(v_j_6_, v_i_5_);
v___x_8_ = l_List_drop___redArg(v_i_5_, v_u_3_);
v___x_9_ = ((lean_object*)(lp_Project_SimonSplit_wordLabeling___redArg___lam__0___closed__0));
lean_inc(v___x_8_);
v___x_10_ = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(v___x_8_, v___x_8_, v___x_7_, v___x_9_);
lean_dec(v___x_8_);
v___x_11_ = lean_apply_1(v_eval_4_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___redArg___lam__0___boxed(lean_object* v_u_12_, lean_object* v_eval_13_, lean_object* v_i_14_, lean_object* v_j_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_Project_SimonSplit_wordLabeling___redArg___lam__0(v_u_12_, v_eval_13_, v_i_14_, v_j_15_);
lean_dec(v_j_15_);
lean_dec(v_u_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___redArg(lean_object* v_eval_17_, lean_object* v_u_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(lp_Project_SimonSplit_wordLabeling___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_19_, 0, v_u_18_);
lean_closure_set(v___f_19_, 1, v_eval_17_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling(lean_object* v_A_20_, lean_object* v_S_21_, lean_object* v_inst_22_, lean_object* v_eval_23_, lean_object* v_hmul_24_, lean_object* v_u_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = lean_alloc_closure((void*)(lp_Project_SimonSplit_wordLabeling___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_26_, 0, v_u_25_);
lean_closure_set(v___f_26_, 1, v_eval_23_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* lp_Project_SimonSplit_wordLabeling___boxed(lean_object* v_A_27_, lean_object* v_S_28_, lean_object* v_inst_29_, lean_object* v_eval_30_, lean_object* v_hmul_31_, lean_object* v_u_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_Project_SimonSplit_wordLabeling(v_A_27_, v_S_28_, v_inst_29_, v_eval_30_, v_hmul_31_, v_u_32_);
lean_dec(v_inst_29_);
return v_res_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Max(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Project_Project_SimonSplit_Basic(uint8_t builtin) {
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
