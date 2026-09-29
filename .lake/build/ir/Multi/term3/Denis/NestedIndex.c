// Lean compiler output
// Module: Multi.term3.Denis.NestedIndex
// Imports: public import Init public meta import Init public import Multi.term3.Denis.ZeroPlateau
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
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_nestedCollapse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NestedIndex_0__T_Correspondence_Denis_Covering_succTerm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NestedIndex_0__T_Correspondence_Denis_Covering_succTerm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_nestedCollapse(lean_object* v_q_1_, lean_object* v_r_2_, lean_object* v_b_3_, lean_object* v_t_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_6_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6_, 0, v_r_2_);
lean_ctor_set(v___x_6_, 1, v_b_3_);
v___x_7_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v_t_4_);
v___x_8_ = lp_Multi_T_Correspondence_Denis_Covering_succTerm(v___x_7_);
v___x_9_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_9_, 0, v_q_1_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
v___x_10_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v_a_5_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NestedIndex_0__T_Correspondence_Denis_Covering_succTerm_match__1_splitter___redArg(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_, lean_object* v_h__3_14_){
_start:
{
switch(lean_obj_tag(v_x_11_))
{
case 0:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_h__3_14_);
lean_dec(v_h__2_13_);
v___x_15_ = lean_box(0);
v___x_16_ = lean_apply_1(v_h__1_12_, v___x_15_);
return v___x_16_;
}
case 1:
{
lean_object* v_a_17_; lean_object* v_b_18_; lean_object* v___x_19_; 
lean_dec(v_h__3_14_);
lean_dec(v_h__1_12_);
v_a_17_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_17_);
v_b_18_ = lean_ctor_get(v_x_11_, 1);
lean_inc(v_b_18_);
lean_dec_ref_known(v_x_11_, 2);
v___x_19_ = lean_apply_2(v_h__2_13_, v_a_17_, v_b_18_);
return v___x_19_;
}
default: 
{
lean_object* v___x_20_; 
lean_dec(v_h__2_13_);
lean_dec(v_h__1_12_);
v___x_20_ = lean_apply_3(v_h__3_14_, v_x_11_, lean_box(0), lean_box(0));
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NestedIndex_0__T_Correspondence_Denis_Covering_succTerm_match__1_splitter(lean_object* v_motive_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_, lean_object* v_h__3_25_){
_start:
{
switch(lean_obj_tag(v_x_22_))
{
case 0:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__3_25_);
lean_dec(v_h__2_24_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__1_23_, v___x_26_);
return v___x_27_;
}
case 1:
{
lean_object* v_a_28_; lean_object* v_b_29_; lean_object* v___x_30_; 
lean_dec(v_h__3_25_);
lean_dec(v_h__1_23_);
v_a_28_ = lean_ctor_get(v_x_22_, 0);
lean_inc(v_a_28_);
v_b_29_ = lean_ctor_get(v_x_22_, 1);
lean_inc(v_b_29_);
lean_dec_ref_known(v_x_22_, 2);
v___x_30_ = lean_apply_2(v_h__2_24_, v_a_28_, v_b_29_);
return v___x_30_;
}
default: 
{
lean_object* v___x_31_; 
lean_dec(v_h__2_24_);
lean_dec(v_h__1_23_);
v___x_31_ = lean_apply_3(v_h__3_25_, v_x_22_, lean_box(0), lean_box(0));
return v___x_31_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_ZeroPlateau(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_NestedIndex(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_ZeroPlateau(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
