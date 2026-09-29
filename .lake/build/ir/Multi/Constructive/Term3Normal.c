// Lean compiler output
// Module: Multi.Constructive.Term3Normal
// Imports: public import Init public meta import Init public import Multi.Constructive.Term3Fundamental
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
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Constructive_Term3Normal_0__T_head_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Constructive_Term3Normal_0__T_head_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_s0_17_; lean_object* v_s1_18_; lean_object* v_s3_19_; lean_object* v___x_20_; uint8_t v___x_21_; uint8_t v___x_22_; 
v_s0_17_ = lean_ctor_get(v_x_15_, 0);
lean_inc_n(v_s0_17_, 2);
v_s1_18_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_s1_18_);
v_s3_19_ = lean_ctor_get(v_x_15_, 3);
lean_inc(v_s3_19_);
lean_dec_ref_known(v_x_15_, 4);
v___x_20_ = lean_alloc_closure((void*)(lp_Multi_instDecidableEqT___boxed), 2, 0);
v___x_21_ = lp_Multi_T_decLt(v_u_14_, v_s0_17_);
lean_inc(v_u_14_);
v___x_22_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v_u_14_, v_s0_17_, v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_dec(v_s1_18_);
lean_dec(v_s0_17_);
v_x_15_ = v_s3_19_;
goto _start;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_box(0);
lean_inc(v_s1_18_);
v___x_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_25_, 0, v_s1_18_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
lean_inc_n(v_u_14_, 2);
v___x_26_ = lp_Multi_T_G_u2081(v_u_14_, v_s0_17_);
v___x_27_ = l_List_appendTR___redArg(v___x_25_, v___x_26_);
v___x_28_ = lp_Multi_T_G_u2081(v_u_14_, v_s1_18_);
v___x_29_ = l_List_appendTR___redArg(v___x_27_, v___x_28_);
v___x_30_ = lp_Multi_T_G_u2081(v_u_14_, v_s3_19_);
v___x_31_ = l_List_appendTR___redArg(v___x_29_, v___x_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_G_u2082(lean_object* v_u_32_, lean_object* v_v_33_, lean_object* v_x_34_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_35_; 
lean_dec(v_v_33_);
lean_dec(v_u_32_);
v___x_35_ = lean_box(0);
return v___x_35_;
}
else
{
lean_object* v_s0_36_; lean_object* v_s1_37_; lean_object* v_s2_38_; lean_object* v_s3_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_63_; 
v_s0_36_ = lean_ctor_get(v_x_34_, 0);
v_s1_37_ = lean_ctor_get(v_x_34_, 1);
v_s2_38_ = lean_ctor_get(v_x_34_, 2);
v_s3_39_ = lean_ctor_get(v_x_34_, 3);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_63_ == 0)
{
v___x_41_ = v_x_34_;
v_isShared_42_ = v_isSharedCheck_63_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_s3_39_);
lean_inc(v_s2_38_);
lean_inc(v_s1_37_);
lean_inc(v_s0_36_);
lean_dec(v_x_34_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_63_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_43_ = lean_box(0);
lean_inc(v_v_33_);
lean_inc(v_u_32_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 3, v___x_43_);
lean_ctor_set(v___x_41_, 2, v___x_43_);
lean_ctor_set(v___x_41_, 1, v_v_33_);
lean_ctor_set(v___x_41_, 0, v_u_32_);
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_u_32_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_v_33_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v___x_43_);
v___x_45_ = v_reuseFailAlloc_62_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; 
lean_inc(v_s1_37_);
lean_inc(v_s0_36_);
v___x_46_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_46_, 0, v_s0_36_);
lean_ctor_set(v___x_46_, 1, v_s1_37_);
lean_ctor_set(v___x_46_, 2, v___x_43_);
lean_ctor_set(v___x_46_, 3, v___x_43_);
v___x_47_ = lean_alloc_closure((void*)(lp_Multi_instDecidableEqT___boxed), 2, 0);
v___x_48_ = lp_Multi_T_decLt(v___x_45_, v___x_46_);
v___x_49_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v___x_45_, v___x_46_, v___x_47_, v___x_48_);
if (v___x_49_ == 0)
{
lean_dec(v_s2_38_);
lean_dec(v_s1_37_);
lean_dec(v_s0_36_);
v_x_34_ = v_s3_39_;
goto _start;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_51_ = lean_box(0);
lean_inc(v_s2_38_);
v___x_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_52_, 0, v_s2_38_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
lean_inc(v_s1_37_);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v_s1_37_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
lean_inc_n(v_v_33_, 3);
lean_inc_n(v_u_32_, 3);
v___x_54_ = lp_Multi_T_G_u2082(v_u_32_, v_v_33_, v_s0_36_);
v___x_55_ = l_List_appendTR___redArg(v___x_53_, v___x_54_);
v___x_56_ = lp_Multi_T_G_u2082(v_u_32_, v_v_33_, v_s1_37_);
v___x_57_ = l_List_appendTR___redArg(v___x_55_, v___x_56_);
v___x_58_ = lp_Multi_T_G_u2082(v_u_32_, v_v_33_, v_s2_38_);
v___x_59_ = l_List_appendTR___redArg(v___x_57_, v___x_58_);
v___x_60_ = lp_Multi_T_G_u2082(v_u_32_, v_v_33_, v_s3_39_);
v___x_61_ = l_List_appendTR___redArg(v___x_59_, v___x_60_);
return v___x_61_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Constructive_Term3Normal_0__T_head_match__1_splitter___redArg(lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_h__2_66_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_1(v_h__1_65_, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v_s0_69_; lean_object* v_s1_70_; lean_object* v_s2_71_; lean_object* v_s3_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_65_);
v_s0_69_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_s0_69_);
v_s1_70_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_s1_70_);
v_s2_71_ = lean_ctor_get(v_x_64_, 2);
lean_inc(v_s2_71_);
v_s3_72_ = lean_ctor_get(v_x_64_, 3);
lean_inc(v_s3_72_);
lean_dec_ref_known(v_x_64_, 4);
v___x_73_ = lean_apply_4(v_h__2_66_, v_s0_69_, v_s1_70_, v_s2_71_, v_s3_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Constructive_Term3Normal_0__T_head_match__1_splitter(lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
if (lean_obj_tag(v_x_75_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_h__2_77_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_h__1_76_, v___x_78_);
return v___x_79_;
}
else
{
lean_object* v_s0_80_; lean_object* v_s1_81_; lean_object* v_s2_82_; lean_object* v_s3_83_; lean_object* v___x_84_; 
lean_dec(v_h__1_76_);
v_s0_80_ = lean_ctor_get(v_x_75_, 0);
lean_inc(v_s0_80_);
v_s1_81_ = lean_ctor_get(v_x_75_, 1);
lean_inc(v_s1_81_);
v_s2_82_ = lean_ctor_get(v_x_75_, 2);
lean_inc(v_s2_82_);
v_s3_83_ = lean_ctor_get(v_x_75_, 3);
lean_inc(v_s3_83_);
lean_dec_ref_known(v_x_75_, 4);
v___x_84_ = lean_apply_4(v_h__2_77_, v_s0_80_, v_s1_81_, v_s2_82_, v_s3_83_);
return v___x_84_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_Constructive_Term3Fundamental(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_Constructive_Term3Normal(uint8_t builtin) {
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
res = initialize_Multi_Multi_Constructive_Term3Fundamental(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
