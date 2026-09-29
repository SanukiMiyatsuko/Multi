// Lean compiler output
// Module: Multi.term3.Denis.Covering
// Imports: public import Init public meta import Init public import Multi.term3.Denis.Source2019
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_array_object lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1___closed__0 = (const lean_object*)&lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_Covering_terms___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_Covering_terms___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_Covering_terms___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_terms(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_terms___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__0(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_a_1_);
v___x_4_ = lean_array_to_list(v_a_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_21_; 
v_head_5_ = lean_ctor_get(v_a_2_, 0);
v_tail_6_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_21_ == 0)
{
v___x_8_ = v_a_2_;
v_isShared_9_ = v_isSharedCheck_21_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_tail_6_);
lean_inc(v_head_5_);
lean_dec(v_a_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_21_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_15_; 
lean_inc_n(v_head_5_, 2);
lean_inc_n(v_a_1_, 3);
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v_a_1_);
lean_ctor_set(v___x_10_, 1, v_head_5_);
v___x_11_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_11_, 0, v_a_1_);
lean_ctor_set(v___x_11_, 1, v_head_5_);
v___x_12_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_12_, 0, v_a_1_);
lean_ctor_set(v___x_12_, 1, v_head_5_);
v___x_13_ = lean_box(0);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v___x_13_);
lean_ctor_set(v___x_8_, 0, v___x_12_);
v___x_15_ = v___x_8_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_12_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v___x_13_);
v___x_15_ = v_reuseFailAlloc_20_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_11_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_10_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
v___x_18_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3_, v___x_17_);
v_a_2_ = v_tail_6_;
v_a_3_ = v___x_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1(lean_object* v___x_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
if (lean_obj_tag(v_a_25_) == 0)
{
lean_object* v___x_27_; 
lean_dec(v___x_24_);
v___x_27_ = lean_array_to_list(v_a_26_);
return v___x_27_;
}
else
{
lean_object* v_head_28_; lean_object* v_tail_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_head_28_ = lean_ctor_get(v_a_25_, 0);
lean_inc(v_head_28_);
v_tail_29_ = lean_ctor_get(v_a_25_, 1);
lean_inc(v_tail_29_);
lean_dec_ref_known(v_a_25_, 2);
v___x_30_ = ((lean_object*)(lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1___closed__0));
lean_inc(v___x_24_);
v___x_31_ = lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__0(v_head_28_, v___x_24_, v___x_30_);
v___x_32_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_26_, v___x_31_);
v_a_25_ = v_tail_29_;
v_a_26_ = v___x_32_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_terms(lean_object* v_x_37_){
_start:
{
lean_object* v_zero_38_; uint8_t v_isZero_39_; 
v_zero_38_ = lean_unsigned_to_nat(0u);
v_isZero_39_ = lean_nat_dec_eq(v_x_37_, v_zero_38_);
if (v_isZero_39_ == 1)
{
lean_object* v___x_40_; 
v___x_40_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_Covering_terms___closed__0));
return v___x_40_;
}
else
{
lean_object* v_one_41_; lean_object* v_n_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_one_41_ = lean_unsigned_to_nat(1u);
v_n_42_ = lean_nat_sub(v_x_37_, v_one_41_);
v___x_43_ = lp_Multi_T_Correspondence_Denis_Covering_terms(v_n_42_);
lean_dec(v_n_42_);
v___x_44_ = ((lean_object*)(lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1___closed__0));
lean_inc_n(v___x_43_, 2);
v___x_45_ = lp_Multi___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00T_Correspondence_Denis_Covering_terms_spec__1(v___x_43_, v___x_43_, v___x_44_);
v___x_46_ = l_List_appendTR___redArg(v___x_43_, v___x_45_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Covering_terms___boxed(lean_object* v_x_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = lp_Multi_T_Correspondence_Denis_Covering_terms(v_x_47_);
lean_dec(v_x_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
lean_object* v_zero_52_; uint8_t v_isZero_53_; 
v_zero_52_ = lean_unsigned_to_nat(0u);
v_isZero_53_ = lean_nat_dec_eq(v_x_49_, v_zero_52_);
if (v_isZero_53_ == 1)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_51_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__1_50_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_one_56_; lean_object* v_n_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_50_);
v_one_56_ = lean_unsigned_to_nat(1u);
v_n_57_ = lean_nat_sub(v_x_49_, v_one_56_);
v___x_58_ = lean_apply_1(v_h__2_51_, v_n_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___redArg___boxed(lean_object* v_x_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___redArg(v_x_59_, v_h__1_60_, v_h__2_61_);
lean_dec(v_x_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter(lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_zero_67_; uint8_t v_isZero_68_; 
v_zero_67_ = lean_unsigned_to_nat(0u);
v_isZero_68_ = lean_nat_dec_eq(v_x_64_, v_zero_67_);
if (v_isZero_68_ == 1)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_66_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__1_65_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v_one_71_; lean_object* v_n_72_; lean_object* v___x_73_; 
lean_dec(v_h__1_65_);
v_one_71_ = lean_unsigned_to_nat(1u);
v_n_72_ = lean_nat_sub(v_x_64_, v_one_71_);
v___x_73_ = lean_apply_1(v_h__2_66_, v_n_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter___boxed(lean_object* v_motive_74_, lean_object* v_x_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = lp_Multi___private_Multi_term3_Denis_Covering_0__T_Correspondence_Denis_Covering_terms_match__1_splitter(v_motive_74_, v_x_75_, v_h__1_76_, v_h__2_77_);
lean_dec(v_x_75_);
return v_res_78_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Denis_Source2019(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_Covering(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Denis_Source2019(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
