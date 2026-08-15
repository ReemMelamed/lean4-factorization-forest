// Lean compiler output
// Module: Project.BrownLemma
// Imports: public import Init public meta import Init public import Mathlib.Algebra.Group.Pointwise.Set.Basic public import Mathlib.Algebra.Group.Hom.Basic public import Mathlib.Algebra.Group.Subsemigroup.Basic public import Mathlib.Data.Set.Finite.Basic public import Mathlib.Data.Set.Finite.Range public import Mathlib.Data.Fintype.Basic public import Mathlib.Algebra.Group.Pointwise.Set.Finite public import Mathlib.Order.CompleteLattice.Finset public import Project.SimonSplit.Combine public import Project.SimonSplit.Split
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
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_BrownLemma_listProdNE___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_BrownLemma_listProdNE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_BrownLemma_listProdNE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_BrownLemma_fiberSubsemigroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_BrownLemma_fiberSubsemigroup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Project_BrownLemma_listProdNE___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_x1_2_, lean_object* v_x2_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_x1_2_, v_x2_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Project_BrownLemma_listProdNE___redArg(lean_object* v_inst_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_head_7_; lean_object* v_tail_8_; lean_object* v___f_9_; lean_object* v___x_10_; 
v_head_7_ = lean_ctor_get(v_x_6_, 0);
lean_inc(v_head_7_);
v_tail_8_ = lean_ctor_get(v_x_6_, 1);
lean_inc(v_tail_8_);
lean_dec(v_x_6_);
v___f_9_ = lean_alloc_closure((void*)(lp_Project_BrownLemma_listProdNE___redArg___lam__0), 3, 1);
lean_closure_set(v___f_9_, 0, v_inst_5_);
v___x_10_ = l_List_foldl___redArg(v___f_9_, v_head_7_, v_tail_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_Project_BrownLemma_listProdNE(lean_object* v_S_11_, lean_object* v_inst_12_, lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lp_Project_BrownLemma_listProdNE___redArg(v_inst_12_, v_x_13_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_Project_BrownLemma_fiberSubsemigroup(lean_object* v_S_16_, lean_object* v_T_17_, lean_object* v_inst_18_, lean_object* v_inst_19_, lean_object* v_f_20_, lean_object* v_e_21_, lean_object* v_he_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_box(0);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_Project_BrownLemma_fiberSubsemigroup___boxed(lean_object* v_S_24_, lean_object* v_T_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_f_28_, lean_object* v_e_29_, lean_object* v_he_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_Project_BrownLemma_fiberSubsemigroup(v_S_24_, v_T_25_, v_inst_26_, v_inst_27_, v_f_28_, v_e_29_, v_he_30_);
lean_dec(v_e_29_);
lean_dec(v_f_28_);
lean_dec(v_inst_27_);
lean_dec(v_inst_26_);
return v_res_31_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Group_Pointwise_Set_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Group_Hom_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Group_Subsemigroup_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Set_Finite_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Set_Finite_Range(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Group_Pointwise_Set_Finite(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_CompleteLattice_Finset(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Combine(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Project_Project_BrownLemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Group_Pointwise_Set_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Group_Hom_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Group_Subsemigroup_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Set_Finite_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Set_Finite_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Group_Pointwise_Set_Finite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_CompleteLattice_Finset(builtin);
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
