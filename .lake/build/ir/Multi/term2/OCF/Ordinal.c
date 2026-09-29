// Lean compiler output
// Module: Multi.term2.OCF.Ordinal
// Imports: public import Init public meta import Init public import Multi.term2.OCF.WellOrder
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
LEAN_EXPORT lean_object* lp_Multi_OCF_WellOrder_isoSetoid;
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_type(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_instLT;
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_instLE;
static lean_object* _init_lp_Multi_OCF_WellOrder_isoSetoid(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_Ordinal_type(lean_object* v_A_2_){
_start:
{
return v_A_2_;
}
}
static lean_object* _init_lp_Multi_OCF_Ordinal_instLT(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
static lean_object* _init_lp_Multi_OCF_Ordinal_instLE(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term2_OCF_WellOrder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term2_OCF_Ordinal(uint8_t builtin) {
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
res = initialize_Multi_Multi_term2_OCF_WellOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Multi_OCF_WellOrder_isoSetoid = _init_lp_Multi_OCF_WellOrder_isoSetoid();
lean_mark_persistent(lp_Multi_OCF_WellOrder_isoSetoid);
lp_Multi_OCF_Ordinal_instLT = _init_lp_Multi_OCF_Ordinal_instLT();
lean_mark_persistent(lp_Multi_OCF_Ordinal_instLT);
lp_Multi_OCF_Ordinal_instLE = _init_lp_Multi_OCF_Ordinal_instLE();
lean_mark_persistent(lp_Multi_OCF_Ordinal_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
