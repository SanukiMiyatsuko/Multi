// Lean compiler output
// Module: Multi.OCF.Supremum
// Imports: public import Init public meta import Init public import Multi.OCF.Range
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
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_supSetoid(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_supSetoid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_supSetoid(lean_object* v_I_1_, lean_object* v_f_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_supSetoid___boxed(lean_object* v_I_4_, lean_object* v_f_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_Multi_OCF_Ordinal_supSetoid(v_I_4_, v_f_5_);
lean_dec(v_f_5_);
return v_res_6_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_OCF_Range(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_OCF_Supremum(uint8_t builtin) {
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
res = initialize_Multi_Multi_OCF_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
