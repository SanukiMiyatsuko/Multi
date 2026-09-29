// Lean compiler output
// Module: Multi.term3.Term3DenisNormal
// Imports: public import Init public meta import Init public import Multi.term3.Term3Denis
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
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_leading(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_leading___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_leading(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 1)
{
lean_object* v_a_2_; 
v_a_2_ = lean_ctor_get(v_x_1_, 0);
v_x_1_ = v_a_2_;
goto _start;
}
else
{
lean_inc(v_x_1_);
return v_x_1_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_leading___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_Multi_T_Correspondence_Denis_Term_leading(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Term3Denis(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Term3DenisNormal(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Term3Denis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
