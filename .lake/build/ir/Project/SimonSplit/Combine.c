// Lean compiler output
// Module: Project.SimonSplit.Combine
// Imports: public import Init public meta import Init public import Mathlib.Data.Fintype.Card public import Mathlib.Data.Finset.Max public import Project.GreensRelations.Order public import Project.SimonSplit.Basic
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
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_2(v_h__1_2_, v_x_1_, lean_box(0));
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter(lean_object* v_S_4_, lean_object* v_strictlyAbove_5_, lean_object* v_motive_6_, lean_object* v_x_7_, lean_object* v_h__1_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_h__1_8_, v_x_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter___boxed(lean_object* v_S_10_, lean_object* v_strictlyAbove_11_, lean_object* v_motive_12_, lean_object* v_x_13_, lean_object* v_h__1_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = lp_Project___private_Project_SimonSplit_Combine_0__SimonSplit_nSElement_match__1_splitter(v_S_10_, v_strictlyAbove_11_, v_motive_12_, v_x_13_, v_h__1_14_);
lean_dec(v_strictlyAbove_11_);
return v_res_15_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Card(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Max(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Order(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Project_Project_SimonSplit_Combine(uint8_t builtin) {
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
res = initialize_Project_Project_SimonSplit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
