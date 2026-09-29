// Lean compiler output
// Module: Multi.term3.Denis.NormalSuccessors
// Imports: public import Init public meta import Init public import Multi.term3.Denis.RevisedCofinality
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
uint8_t lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_succTerm(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_predTerm(lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalSuccessors_0__T_Correspondence_Denis_Covering_predTerm_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalSuccessors_0__T_Correspondence_Denis_Covering_predTerm_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_succTerm(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lp_Multi_T_Correspondence_Denis_one;
return v___x_2_;
}
case 1:
{
lean_object* v_a_3_; lean_object* v_b_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_a_3_ = lean_ctor_get(v_x_1_, 0);
v_b_4_ = lean_ctor_get(v_x_1_, 1);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_12_ == 0)
{
v___x_6_ = v_x_1_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_b_4_);
lean_inc(v_a_3_);
lean_dec(v_x_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_8_ = lp_Multi_T_Correspondence_Denis_Covering_succTerm(v_b_4_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_a_3_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v___x_8_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
default: 
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lp_Multi_T_Correspondence_Denis_one;
v___x_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_14_, 0, v_x_1_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_predTerm(lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 1)
{
lean_object* v_a_16_; lean_object* v_b_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_27_; 
v_a_16_ = lean_ctor_get(v_x_15_, 0);
v_b_17_ = lean_ctor_get(v_x_15_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_27_ == 0)
{
v___x_19_ = v_x_15_;
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_b_17_);
lean_inc(v_a_16_);
lean_dec(v_x_15_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_21_ = lp_Multi_T_Correspondence_Denis_Covering_predTerm(v_b_17_);
v___x_22_ = lean_box(0);
v___x_23_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_25_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v___x_21_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_16_);
lean_ctor_set(v_reuseFailAlloc_26_, 1, v___x_21_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
else
{
lean_dec(v___x_21_);
lean_del_object(v___x_19_);
return v_a_16_;
}
}
}
else
{
lean_object* v___x_28_; 
lean_dec(v_x_15_);
v___x_28_ = lean_box(0);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalSuccessors_0__T_Correspondence_Denis_Covering_predTerm_match__1_splitter___redArg(lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
if (lean_obj_tag(v_x_29_) == 1)
{
lean_object* v_a_32_; lean_object* v_b_33_; lean_object* v___x_34_; 
lean_dec(v_h__2_31_);
v_a_32_ = lean_ctor_get(v_x_29_, 0);
lean_inc(v_a_32_);
v_b_33_ = lean_ctor_get(v_x_29_, 1);
lean_inc(v_b_33_);
lean_dec_ref_known(v_x_29_, 2);
v___x_34_ = lean_apply_2(v_h__1_30_, v_a_32_, v_b_33_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; 
lean_dec(v_h__1_30_);
v___x_35_ = lean_apply_2(v_h__2_31_, v_x_29_, lean_box(0));
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_NormalSuccessors_0__T_Correspondence_Denis_Covering_predTerm_match__1_splitter(lean_object* v_motive_36_, lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 1)
{
lean_object* v_a_40_; lean_object* v_b_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_39_);
v_a_40_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_a_40_);
v_b_41_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_b_41_);
lean_dec_ref_known(v_x_37_, 2);
v___x_42_ = lean_apply_2(v_h__1_38_, v_a_40_, v_b_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
lean_dec(v_h__1_38_);
v___x_43_ = lean_apply_2(v_h__2_39_, v_x_37_, lean_box(0));
return v___x_43_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_RevisedCofinality(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_NormalSuccessors(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_RevisedCofinality(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
