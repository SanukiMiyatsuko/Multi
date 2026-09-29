// Lean compiler output
// Module: Multi.term3.Denis.RevisedNormal
// Imports: public import Init public meta import Init public import Multi.term3.Denis.RevisedSequences
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
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_canonicalWellOrder(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_rankTowerTerm(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_rankTowerTerm___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_canonicalWellOrder(lean_object* v_s_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_rankTowerTerm(lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
else
{
lean_object* v_one_7_; lean_object* v_n_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_one_7_ = lean_unsigned_to_nat(1u);
v_n_8_ = lean_nat_sub(v_x_3_, v_one_7_);
v___x_9_ = lp_Multi_T_Correspondence_Denis_Covering_rankTowerTerm(v_n_8_);
lean_dec(v_n_8_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_rankTowerTerm___boxed(lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_Multi_T_Correspondence_Denis_Covering_rankTowerTerm(v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_RevisedSequences(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_RevisedNormal(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_RevisedSequences(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
