// Lean compiler output
// Module: Multi.term3.Term3DenisOrder
// Imports: public import Init public meta import Init public import Multi.term3.Term3DenisNormal public import Multi.term3.Denis.RankBound
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_indexIterTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_indexIterTerm___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_normalOrdinalWellOrder(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_indexIterTerm(lean_object* v_r_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_zero_3_; uint8_t v_isZero_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v_isZero_4_ = lean_nat_dec_eq(v_x_2_, v_zero_3_);
if (v_isZero_4_ == 1)
{
lean_object* v___x_5_; 
lean_dec(v_r_1_);
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_2_, v_one_6_);
lean_inc(v_r_1_);
v___x_8_ = lp_Multi_T_Correspondence_Denis_indexIterTerm(v_r_1_, v_n_7_);
lean_dec(v_n_7_);
v___x_9_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_9_, 0, v_r_1_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_indexIterTerm___boxed(lean_object* v_r_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_Multi_T_Correspondence_Denis_indexIterTerm(v_r_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_normalOrdinalWellOrder(lean_object* v_s_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Term3DenisNormal(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_RankBound(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Term3DenisOrder(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Term3DenisNormal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Multi_Multi_term3_Denis_RankBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
