// Lean compiler output
// Module: Multi.term3.Denis.WellDefined
// Imports: public import Init public meta import Init public import Multi.term3.Denis.Collapse public import Multi.term3.Denis.Small
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
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_5_ = lean_box(0);
v___x_6_ = lean_apply_1(v_h__1_2_, v___x_5_);
return v___x_6_;
}
case 1:
{
lean_object* v_x_7_; lean_object* v___x_8_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_x_7_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_x_7_);
lean_dec_ref_known(v_x_1_, 1);
v___x_8_ = lean_apply_1(v_h__2_3_, v_x_7_);
return v___x_8_;
}
default: 
{
lean_object* v_op_9_; lean_object* v_left_10_; lean_object* v_right_11_; lean_object* v___x_12_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v_op_9_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_op_9_);
v_left_10_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_left_10_);
v_right_11_ = lean_ctor_get(v_x_1_, 2);
lean_inc(v_right_11_);
lean_dec_ref_known(v_x_1_, 3);
v___x_12_ = lean_apply_3(v_h__3_4_, v_op_9_, v_left_10_, v_right_11_);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter(lean_object* v_beta_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
v___x_19_ = lean_box(0);
v___x_20_ = lean_apply_1(v_h__1_16_, v___x_19_);
return v___x_20_;
}
case 1:
{
lean_object* v_x_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__1_16_);
v_x_21_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_x_21_);
lean_dec_ref_known(v_x_15_, 1);
v___x_22_ = lean_apply_1(v_h__2_17_, v_x_21_);
return v___x_22_;
}
default: 
{
lean_object* v_op_23_; lean_object* v_left_24_; lean_object* v_right_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_17_);
lean_dec(v_h__1_16_);
v_op_23_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_op_23_);
v_left_24_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_left_24_);
v_right_25_ = lean_ctor_get(v_x_15_, 2);
lean_inc(v_right_25_);
lean_dec_ref_known(v_x_15_, 3);
v___x_26_ = lean_apply_3(v_h__3_18_, v_op_23_, v_left_24_, v_right_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter___boxed(lean_object* v_beta_27_, lean_object* v_motive_28_, lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_, lean_object* v_h__3_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_Multi___private_Multi_term3_Denis_WellDefined_0__OCF_Denis_evaluate_match__1_splitter(v_beta_27_, v_motive_28_, v_x_29_, v_h__1_30_, v_h__2_31_, v_h__3_32_);
lean_dec(v_beta_27_);
return v_res_33_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_Collapse(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_Small(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_WellDefined(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_Collapse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Multi_Multi_term3_Denis_Small(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
