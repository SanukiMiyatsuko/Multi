// Lean compiler output
// Module: Multi.term3.Denis.CollapseTrees
// Imports: public import Init public meta import Init public import Multi.term3.Denis.SuccessorRankClosure
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
lean_object* lp_Multi_T_Correspondence_Denis_Covering_succTerm(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_successorRankCollapseTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_successorRankCollapseTerm(lean_object* v_r_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lp_Multi_T_Correspondence_Denis_Covering_succTerm(v_r_1_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_3_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
v___x_6_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v_a_2_);
return v___x_6_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_SuccessorRankClosure(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_CollapseTrees(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Multi_Multi_term3_Denis_SuccessorRankClosure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
