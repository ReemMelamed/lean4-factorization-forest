// Lean compiler output
// Module: Project
// Imports: public import Init public meta import Init public import Project.GreensRelations.Basic public import Project.SimonSplit.Basic public import Project.SimonSplit.Combine public import Project.SimonSplit.Irregular public import Project.SimonSplit.Regular public import Project.SimonSplit.Split public import Project.GreensRelations.MulSeq public import Project.GreensRelations.Order public import Project.GreensRelations.Green public import Project.GreensRelations.Finite public import Project.BrownLemma public import Project.SimonSplit.FactorizationTree
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Basic(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Basic(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Combine(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Irregular(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Regular(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_Split(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_MulSeq(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Order(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Green(uint8_t builtin);
lean_object* initialize_Project_Project_GreensRelations_Finite(uint8_t builtin);
lean_object* initialize_Project_Project_BrownLemma(uint8_t builtin);
lean_object* initialize_Project_Project_SimonSplit_FactorizationTree(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Project_Project(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_GreensRelations_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Combine(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Irregular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Regular(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_GreensRelations_MulSeq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_GreensRelations_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_GreensRelations_Green(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_GreensRelations_Finite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_BrownLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Project_Project_SimonSplit_FactorizationTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
