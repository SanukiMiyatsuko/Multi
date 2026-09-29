// Lean compiler output
// Module: Multi.term3.Denis.NormalAddition
// Imports: public import Init public meta import Init public import Multi.term3.Denis.NormalSuccessors public import Multi.term3.Denis.TransfiniteRules
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
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_Covering_addTerm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_Covering_addTerm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_Covering_addTerm_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_, lean_object* v_h__4_6_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_7_; 
lean_dec(v_h__4_6_);
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_7_ = lean_apply_1(v_h__1_3_, v_x_1_);
return v___x_7_;
}
else
{
lean_dec(v_h__1_3_);
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_8_; 
lean_dec(v_h__4_6_);
lean_dec(v_h__3_5_);
v___x_8_ = lean_apply_2(v_h__2_4_, v_x_2_, lean_box(0));
return v___x_8_;
}
case 1:
{
lean_object* v_a_9_; lean_object* v_b_10_; lean_object* v___x_11_; 
lean_dec(v_h__4_6_);
lean_dec(v_h__2_4_);
v_a_9_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_9_);
v_b_10_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_b_10_);
lean_dec_ref_known(v_x_1_, 2);
v___x_11_ = lean_apply_4(v_h__3_5_, v_a_9_, v_b_10_, v_x_2_, lean_box(0));
return v___x_11_;
}
default: 
{
lean_object* v___x_12_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_12_ = lean_apply_5(v_h__4_6_, v_x_1_, v_x_2_, lean_box(0), lean_box(0), lean_box(0));
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_Covering_addTerm_match__1_splitter(lean_object* v_motive_13_, lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_, lean_object* v_h__4_19_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_20_; 
lean_dec(v_h__4_19_);
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
v___x_20_ = lean_apply_1(v_h__1_16_, v_x_14_);
return v___x_20_;
}
else
{
lean_dec(v_h__1_16_);
switch(lean_obj_tag(v_x_14_))
{
case 0:
{
lean_object* v___x_21_; 
lean_dec(v_h__4_19_);
lean_dec(v_h__3_18_);
v___x_21_ = lean_apply_2(v_h__2_17_, v_x_15_, lean_box(0));
return v___x_21_;
}
case 1:
{
lean_object* v_a_22_; lean_object* v_b_23_; lean_object* v___x_24_; 
lean_dec(v_h__4_19_);
lean_dec(v_h__2_17_);
v_a_22_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_22_);
v_b_23_ = lean_ctor_get(v_x_14_, 1);
lean_inc(v_b_23_);
lean_dec_ref_known(v_x_14_, 2);
v___x_24_ = lean_apply_4(v_h__3_18_, v_a_22_, v_b_23_, v_x_15_, lean_box(0));
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
v___x_25_ = lean_apply_5(v_h__4_19_, v_x_14_, v_x_15_, lean_box(0), lean_box(0), lean_box(0));
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_denote_match__1_splitter___redArg(lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_, lean_object* v_h__3_29_, lean_object* v_h__4_30_){
_start:
{
switch(lean_obj_tag(v_x_26_))
{
case 0:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__4_30_);
lean_dec(v_h__3_29_);
lean_dec(v_h__2_28_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__1_27_, v___x_31_);
return v___x_32_;
}
case 1:
{
lean_object* v_a_33_; lean_object* v_b_34_; lean_object* v___x_35_; 
lean_dec(v_h__4_30_);
lean_dec(v_h__3_29_);
lean_dec(v_h__1_27_);
v_a_33_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_33_);
v_b_34_ = lean_ctor_get(v_x_26_, 1);
lean_inc(v_b_34_);
lean_dec_ref_known(v_x_26_, 2);
v___x_35_ = lean_apply_2(v_h__2_28_, v_a_33_, v_b_34_);
return v___x_35_;
}
case 2:
{
lean_object* v_a_36_; lean_object* v_b_37_; lean_object* v___x_38_; 
lean_dec(v_h__4_30_);
lean_dec(v_h__2_28_);
lean_dec(v_h__1_27_);
v_a_36_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_36_);
v_b_37_ = lean_ctor_get(v_x_26_, 1);
lean_inc(v_b_37_);
lean_dec_ref_known(v_x_26_, 2);
v___x_38_ = lean_apply_2(v_h__3_29_, v_a_36_, v_b_37_);
return v___x_38_;
}
default: 
{
lean_object* v_k_39_; lean_object* v_a_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_29_);
lean_dec(v_h__2_28_);
lean_dec(v_h__1_27_);
v_k_39_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_k_39_);
v_a_40_ = lean_ctor_get(v_x_26_, 1);
lean_inc(v_a_40_);
lean_dec_ref_known(v_x_26_, 2);
v___x_41_ = lean_apply_2(v_h__4_30_, v_k_39_, v_a_40_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalAddition_0__T_Correspondence_Denis_denote_match__1_splitter(lean_object* v_motive_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_, lean_object* v_h__4_47_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_44_, v___x_48_);
return v___x_49_;
}
case 1:
{
lean_object* v_a_50_; lean_object* v_b_51_; lean_object* v___x_52_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v_a_50_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_a_50_);
v_b_51_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_b_51_);
lean_dec_ref_known(v_x_43_, 2);
v___x_52_ = lean_apply_2(v_h__2_45_, v_a_50_, v_b_51_);
return v___x_52_;
}
case 2:
{
lean_object* v_a_53_; lean_object* v_b_54_; lean_object* v___x_55_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_a_53_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_a_53_);
v_b_54_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_b_54_);
lean_dec_ref_known(v_x_43_, 2);
v___x_55_ = lean_apply_2(v_h__3_46_, v_a_53_, v_b_54_);
return v___x_55_;
}
default: 
{
lean_object* v_k_56_; lean_object* v_a_57_; lean_object* v___x_58_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_k_56_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_k_56_);
v_a_57_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_a_57_);
lean_dec_ref_known(v_x_43_, 2);
v___x_58_ = lean_apply_2(v_h__4_47_, v_k_56_, v_a_57_);
return v___x_58_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_NormalSuccessors(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_TransfiniteRules(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_NormalAddition(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_NormalSuccessors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Multi_Multi_term3_Denis_TransfiniteRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
