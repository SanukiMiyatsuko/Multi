// Lean compiler output
// Module: Multi.term3.Term3Normal
// Imports: public import Init public meta import Init public import Multi.term3.Term3Fundamental
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
lean_object* lp_Multi_instDecidableEqT___boxed(lean_object*, lean_object*);
uint8_t lp_Multi_T_decLt(lean_object*, lean_object*);
uint8_t lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_head(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_G_u2081(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_G_u2082(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Normal_0__T_head_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Normal_0__T_head_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_head(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
return v_x_1_;
}
else
{
lean_object* v_s0_2_; lean_object* v_s1_3_; lean_object* v_s2_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_s0_2_ = lean_ctor_get(v_x_1_, 0);
v_s1_3_ = lean_ctor_get(v_x_1_, 1);
v_s2_4_ = lean_ctor_get(v_x_1_, 2);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_12_ == 0)
{
lean_object* v_unused_13_; 
v_unused_13_ = lean_ctor_get(v_x_1_, 3);
lean_dec(v_unused_13_);
v___x_6_ = v_x_1_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_s2_4_);
lean_inc(v_s1_3_);
lean_inc(v_s0_2_);
lean_dec(v_x_1_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 3, v___x_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v_s0_2_);
lean_ctor_set(v_reuseFailAlloc_11_, 1, v_s1_3_);
lean_ctor_set(v_reuseFailAlloc_11_, 2, v_s2_4_);
lean_ctor_set(v_reuseFailAlloc_11_, 3, v___x_8_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_G_u2081(lean_object* v_u_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
lean_object* v___x_16_; 
lean_dec(v_u_14_);
v___x_16_ = lean_box(0);
return v___x_16_;
}
else
{
lean_object* v_s0_17_; lean_object* v_s1_18_; lean_object* v_s2_19_; lean_object* v_s3_20_; lean_object* v___x_21_; uint8_t v___x_22_; uint8_t v___x_23_; 
v_s0_17_ = lean_ctor_get(v_x_15_, 0);
lean_inc_n(v_s0_17_, 2);
v_s1_18_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_s1_18_);
v_s2_19_ = lean_ctor_get(v_x_15_, 2);
lean_inc(v_s2_19_);
v_s3_20_ = lean_ctor_get(v_x_15_, 3);
lean_inc(v_s3_20_);
lean_dec_ref_known(v_x_15_, 4);
v___x_21_ = lean_alloc_closure((void*)(lp_Multi_instDecidableEqT___boxed), 2, 0);
v___x_22_ = lp_Multi_T_decLt(v_u_14_, v_s0_17_);
lean_inc(v_u_14_);
v___x_23_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v_u_14_, v_s0_17_, v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_dec(v_s2_19_);
lean_dec(v_s1_18_);
lean_dec(v_s0_17_);
v_x_15_ = v_s3_20_;
goto _start;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_25_ = lean_box(0);
lean_inc(v_s1_18_);
v___x_26_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_26_, 0, v_s1_18_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_inc_n(v_u_14_, 3);
v___x_27_ = lp_Multi_T_G_u2081(v_u_14_, v_s0_17_);
v___x_28_ = l_List_appendTR___redArg(v___x_26_, v___x_27_);
v___x_29_ = lp_Multi_T_G_u2081(v_u_14_, v_s1_18_);
v___x_30_ = l_List_appendTR___redArg(v___x_28_, v___x_29_);
v___x_31_ = lp_Multi_T_G_u2081(v_u_14_, v_s2_19_);
v___x_32_ = l_List_appendTR___redArg(v___x_30_, v___x_31_);
v___x_33_ = lp_Multi_T_G_u2081(v_u_14_, v_s3_20_);
v___x_34_ = l_List_appendTR___redArg(v___x_32_, v___x_33_);
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_G_u2082(lean_object* v_u_35_, lean_object* v_v_36_, lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_38_; 
lean_dec(v_v_36_);
lean_dec(v_u_35_);
v___x_38_ = lean_box(0);
return v___x_38_;
}
else
{
lean_object* v_s0_39_; lean_object* v_s1_40_; lean_object* v_s2_41_; lean_object* v_s3_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_66_; 
v_s0_39_ = lean_ctor_get(v_x_37_, 0);
v_s1_40_ = lean_ctor_get(v_x_37_, 1);
v_s2_41_ = lean_ctor_get(v_x_37_, 2);
v_s3_42_ = lean_ctor_get(v_x_37_, 3);
v_isSharedCheck_66_ = !lean_is_exclusive(v_x_37_);
if (v_isSharedCheck_66_ == 0)
{
v___x_44_ = v_x_37_;
v_isShared_45_ = v_isSharedCheck_66_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_s3_42_);
lean_inc(v_s2_41_);
lean_inc(v_s1_40_);
lean_inc(v_s0_39_);
lean_dec(v_x_37_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_66_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
lean_inc(v_v_36_);
lean_inc(v_u_35_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 3, v___x_46_);
lean_ctor_set(v___x_44_, 2, v___x_46_);
lean_ctor_set(v___x_44_, 1, v_v_36_);
lean_ctor_set(v___x_44_, 0, v_u_35_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_u_35_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_v_36_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v___x_46_);
v___x_48_ = v_reuseFailAlloc_65_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; 
lean_inc(v_s1_40_);
lean_inc(v_s0_39_);
v___x_49_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_49_, 0, v_s0_39_);
lean_ctor_set(v___x_49_, 1, v_s1_40_);
lean_ctor_set(v___x_49_, 2, v___x_46_);
lean_ctor_set(v___x_49_, 3, v___x_46_);
v___x_50_ = lean_alloc_closure((void*)(lp_Multi_instDecidableEqT___boxed), 2, 0);
v___x_51_ = lp_Multi_T_decLt(v___x_48_, v___x_49_);
v___x_52_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v___x_48_, v___x_49_, v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
lean_dec(v_s2_41_);
lean_dec(v_s1_40_);
lean_dec(v_s0_39_);
v_x_37_ = v_s3_42_;
goto _start;
}
else
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_54_ = lean_box(0);
lean_inc(v_s2_41_);
v___x_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_55_, 0, v_s2_41_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
lean_inc(v_s1_40_);
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v_s1_40_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
lean_inc_n(v_v_36_, 3);
lean_inc_n(v_u_35_, 3);
v___x_57_ = lp_Multi_T_G_u2082(v_u_35_, v_v_36_, v_s0_39_);
v___x_58_ = l_List_appendTR___redArg(v___x_56_, v___x_57_);
v___x_59_ = lp_Multi_T_G_u2082(v_u_35_, v_v_36_, v_s1_40_);
v___x_60_ = l_List_appendTR___redArg(v___x_58_, v___x_59_);
v___x_61_ = lp_Multi_T_G_u2082(v_u_35_, v_v_36_, v_s2_41_);
v___x_62_ = l_List_appendTR___redArg(v___x_60_, v___x_61_);
v___x_63_ = lp_Multi_T_G_u2082(v_u_35_, v_v_36_, v_s3_42_);
v___x_64_ = l_List_appendTR___redArg(v___x_62_, v___x_63_);
return v___x_64_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Normal_0__T_head_match__1_splitter___redArg(lean_object* v_x_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__2_69_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__1_68_, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_s0_72_; lean_object* v_s1_73_; lean_object* v_s2_74_; lean_object* v_s3_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_68_);
v_s0_72_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_s0_72_);
v_s1_73_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_s1_73_);
v_s2_74_ = lean_ctor_get(v_x_67_, 2);
lean_inc(v_s2_74_);
v_s3_75_ = lean_ctor_get(v_x_67_, 3);
lean_inc(v_s3_75_);
lean_dec_ref_known(v_x_67_, 4);
v___x_76_ = lean_apply_4(v_h__2_69_, v_s0_72_, v_s1_73_, v_s2_74_, v_s3_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Normal_0__T_head_match__1_splitter(lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_x_78_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__2_80_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__1_79_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_s0_83_; lean_object* v_s1_84_; lean_object* v_s2_85_; lean_object* v_s3_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_79_);
v_s0_83_ = lean_ctor_get(v_x_78_, 0);
lean_inc(v_s0_83_);
v_s1_84_ = lean_ctor_get(v_x_78_, 1);
lean_inc(v_s1_84_);
v_s2_85_ = lean_ctor_get(v_x_78_, 2);
lean_inc(v_s2_85_);
v_s3_86_ = lean_ctor_get(v_x_78_, 3);
lean_inc(v_s3_86_);
lean_dec_ref_known(v_x_78_, 4);
v___x_87_ = lean_apply_4(v_h__2_80_, v_s0_83_, v_s1_84_, v_s2_85_, v_s3_86_);
return v___x_87_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Term3Fundamental(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Term3Normal(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Term3Fundamental(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
