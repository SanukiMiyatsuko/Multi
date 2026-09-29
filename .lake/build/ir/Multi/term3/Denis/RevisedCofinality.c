// Lean compiler output
// Module: Multi.term3.Denis.RevisedCofinality
// Imports: public import Init public meta import Init public import Multi.term3.Denis.RevisedNormal
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
extern lean_object* lp_Multi_T_Correspondence_Denis_one;
lean_object* lp_Multi_T_Correspondence_Denis_Source2019_repeatTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_finiteTerm(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_finiteTerm___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_finiteTerm(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lp_Multi_T_Correspondence_Denis_one;
v___x_3_ = lp_Multi_T_Correspondence_Denis_Source2019_repeatTerm(v___x_2_, v_n_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_finiteTerm___boxed(lean_object* v_n_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_Multi_T_Correspondence_Denis_Covering_finiteTerm(v_n_4_);
lean_dec(v_n_4_);
return v_res_5_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_RevisedNormal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_RevisedCofinality(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_RevisedNormal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
