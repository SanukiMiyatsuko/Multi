// Lean compiler output
// Module: Multi.term2.OCF.Range
// Imports: public import Init public meta import Init public import Multi.term2.OCF.Ordinal
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
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_orderOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_orderOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_orderOn(lean_object* v_X_1_, lean_object* v_f_2_, lean_object* v_hf_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_orderOn___boxed(lean_object* v_X_5_, lean_object* v_f_6_, lean_object* v_hf_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_Multi_OCF_Ordinal_orderOn(v_X_5_, v_f_6_, v_hf_7_);
lean_dec(v_f_6_);
return v_res_8_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term2_OCF_Ordinal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term2_OCF_Range(uint8_t builtin) {
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
res = initialize_Multi_Multi_term2_OCF_Ordinal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
