// Lean compiler output
// Module: Multi.Term3
// Imports: public import Init public meta import Init public import Multi.order
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Z_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Z_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_P_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_P_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_instDecidableEqT_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_instDecidableEqT_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_instDecidableEqT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_instDecidableEqT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_instLTT;
LEAN_EXPORT uint8_t lp_Multi_T_decLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_instDecidableLtT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_instDecidableLtT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_add___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Multi_instAddT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Multi_T_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Multi_instAddT___closed__0 = (const lean_object*)&lp_Multi_instAddT___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_instAddT = (const lean_object*)&lp_Multi_instAddT___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_iter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_size(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_size___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_Zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_Zero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_One_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_One_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03c9_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03c9_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03a9_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03a9_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_T_instDecidableEqDom_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_instDecidableEqDom_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_T_instDecidableEqDom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_instDecidableEqDom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_dom(lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_iter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_iter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_dom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_dom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_fund_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_fund_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_LF(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_LF___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_Multi_T_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_s0_8_; lean_object* v_s1_9_; lean_object* v_s2_10_; lean_object* v_s3_11_; lean_object* v___x_12_; 
v_s0_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_s0_8_);
v_s1_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_s1_9_);
v_s2_10_ = lean_ctor_get(v_t_6_, 2);
lean_inc(v_s2_10_);
v_s3_11_ = lean_ctor_get(v_t_6_, 3);
lean_inc(v_s3_11_);
lean_dec_ref_known(v_t_6_, 4);
v___x_12_ = lean_apply_4(v_k_7_, v_s0_8_, v_s1_9_, v_s2_10_, v_s3_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_Multi_T_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_Multi_T_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Z_elim___redArg(lean_object* v_t_25_, lean_object* v_Z_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_Multi_T_ctorElim___redArg(v_t_25_, v_Z_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Z_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_Z_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_Multi_T_ctorElim___redArg(v_t_29_, v_Z_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_P_elim___redArg(lean_object* v_t_33_, lean_object* v_P_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lp_Multi_T_ctorElim___redArg(v_t_33_, v_P_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_P_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_P_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_Multi_T_ctorElim___redArg(v_t_37_, v_P_39_);
return v___x_40_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableEqT_decEq(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
if (lean_obj_tag(v_x_42_) == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 1;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 0;
return v___x_44_;
}
}
else
{
lean_object* v_s0_45_; lean_object* v_s1_46_; lean_object* v_s2_47_; lean_object* v_s3_48_; uint8_t v___x_49_; 
v_s0_45_ = lean_ctor_get(v_x_41_, 0);
v_s1_46_ = lean_ctor_get(v_x_41_, 1);
v_s2_47_ = lean_ctor_get(v_x_41_, 2);
v_s3_48_ = lean_ctor_get(v_x_41_, 3);
v___x_49_ = 0;
if (lean_obj_tag(v_x_42_) == 0)
{
return v___x_49_;
}
else
{
lean_object* v_s0_50_; lean_object* v_s1_51_; lean_object* v_s2_52_; lean_object* v_s3_53_; uint8_t v_inst_54_; 
v_s0_50_ = lean_ctor_get(v_x_42_, 0);
v_s1_51_ = lean_ctor_get(v_x_42_, 1);
v_s2_52_ = lean_ctor_get(v_x_42_, 2);
v_s3_53_ = lean_ctor_get(v_x_42_, 3);
v_inst_54_ = lp_Multi_instDecidableEqT_decEq(v_s0_45_, v_s0_50_);
if (v_inst_54_ == 0)
{
return v___x_49_;
}
else
{
uint8_t v_inst_55_; 
v_inst_55_ = lp_Multi_instDecidableEqT_decEq(v_s1_46_, v_s1_51_);
if (v_inst_55_ == 0)
{
return v___x_49_;
}
else
{
uint8_t v_inst_56_; 
v_inst_56_ = lp_Multi_instDecidableEqT_decEq(v_s2_47_, v_s2_52_);
if (v_inst_56_ == 0)
{
return v___x_49_;
}
else
{
uint8_t v_inst_57_; 
v_inst_57_ = lp_Multi_instDecidableEqT_decEq(v_s3_48_, v_s3_53_);
if (v_inst_57_ == 0)
{
return v___x_49_;
}
else
{
return v_inst_57_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableEqT_decEq___boxed(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = lp_Multi_instDecidableEqT_decEq(v_x_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_x_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableEqT(lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
uint8_t v___x_64_; 
v___x_64_ = lp_Multi_instDecidableEqT_decEq(v_x_62_, v_x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableEqT___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = lp_Multi_instDecidableEqT(v_x_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_x_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
static lean_object* _init_lp_Multi_instLTT(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_decLt(lean_object* v_a_70_, lean_object* v_b_71_){
_start:
{
if (lean_obj_tag(v_a_70_) == 0)
{
if (lean_obj_tag(v_b_71_) == 0)
{
uint8_t v___x_72_; 
v___x_72_ = 0;
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
v___x_73_ = 1;
return v___x_73_;
}
}
else
{
lean_object* v_s0_74_; lean_object* v_s1_75_; lean_object* v_s2_76_; lean_object* v_s3_77_; uint8_t v___x_78_; 
v_s0_74_ = lean_ctor_get(v_a_70_, 0);
v_s1_75_ = lean_ctor_get(v_a_70_, 1);
v_s2_76_ = lean_ctor_get(v_a_70_, 2);
v_s3_77_ = lean_ctor_get(v_a_70_, 3);
v___x_78_ = 0;
if (lean_obj_tag(v_b_71_) == 0)
{
return v___x_78_;
}
else
{
lean_object* v_s0_79_; lean_object* v_s1_80_; lean_object* v_s2_81_; lean_object* v_s3_82_; uint8_t v___x_83_; uint8_t v___x_84_; 
v_s0_79_ = lean_ctor_get(v_b_71_, 0);
v_s1_80_ = lean_ctor_get(v_b_71_, 1);
v_s2_81_ = lean_ctor_get(v_b_71_, 2);
v_s3_82_ = lean_ctor_get(v_b_71_, 3);
v___x_83_ = lp_Multi_instDecidableEqT_decEq(v_s0_74_, v_s0_79_);
v___x_84_ = lp_Multi_T_decLt(v_s0_74_, v_s0_79_);
if (v___x_84_ == 0)
{
if (v___x_83_ == 0)
{
return v___x_78_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = lp_Multi_T_decLt(v_s1_75_, v_s1_80_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = lp_Multi_instDecidableEqT_decEq(v_s1_75_, v_s1_80_);
if (v___x_86_ == 0)
{
return v___x_78_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = lp_Multi_T_decLt(v_s2_76_, v_s2_81_);
if (v___x_87_ == 0)
{
uint8_t v___x_88_; 
v___x_88_ = lp_Multi_instDecidableEqT_decEq(v_s2_76_, v_s2_81_);
if (v___x_88_ == 0)
{
return v___x_78_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = lp_Multi_T_decLt(v_s3_77_, v_s3_82_);
if (v___x_89_ == 0)
{
return v___x_78_;
}
else
{
return v___x_89_;
}
}
}
else
{
return v___x_87_;
}
}
}
else
{
return v___x_85_;
}
}
}
else
{
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_decLt___boxed(lean_object* v_a_90_, lean_object* v_b_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = lp_Multi_T_decLt(v_a_90_, v_b_91_);
lean_dec(v_b_91_);
lean_dec(v_a_90_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableLtT(lean_object* v_a_94_, lean_object* v_b_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lp_Multi_T_decLt(v_a_94_, v_b_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableLtT___boxed(lean_object* v_a_97_, lean_object* v_b_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = lp_Multi_instDecidableLtT(v_a_97_, v_b_98_);
lean_dec(v_b_98_);
lean_dec(v_a_97_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_add(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_inc(v_x_102_);
return v_x_102_;
}
else
{
if (lean_obj_tag(v_x_102_) == 0)
{
return v_x_101_;
}
else
{
lean_object* v_s0_103_; lean_object* v_s1_104_; lean_object* v_s2_105_; lean_object* v_s3_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_114_; 
v_s0_103_ = lean_ctor_get(v_x_101_, 0);
v_s1_104_ = lean_ctor_get(v_x_101_, 1);
v_s2_105_ = lean_ctor_get(v_x_101_, 2);
v_s3_106_ = lean_ctor_get(v_x_101_, 3);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_101_);
if (v_isSharedCheck_114_ == 0)
{
v___x_108_ = v_x_101_;
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_s3_106_);
lean_inc(v_s2_105_);
lean_inc(v_s1_104_);
lean_inc(v_s0_103_);
lean_dec(v_x_101_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_110_ = lp_Multi_T_add(v_s3_106_, v_x_102_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 3, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_s0_103_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_s1_104_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_s2_105_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_add___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = lp_Multi_T_add(v_x_115_, v_x_116_);
lean_dec(v_x_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_mul(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
return v_x_121_;
}
else
{
lean_object* v_s3_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_s3_122_ = lean_ctor_get(v_x_121_, 3);
v___x_123_ = lp_Multi_T_mul(v_x_120_, v_s3_122_);
v___x_124_ = lp_Multi_T_add(v___x_123_, v_x_120_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_mul___boxed(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_Multi_T_mul(v_x_125_, v_x_126_);
lean_dec(v_x_126_);
lean_dec(v_x_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_iter(lean_object* v_F_128_, lean_object* v_x_129_){
_start:
{
if (lean_obj_tag(v_x_129_) == 0)
{
lean_dec_ref(v_F_128_);
return v_x_129_;
}
else
{
lean_object* v_s3_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_s3_130_ = lean_ctor_get(v_x_129_, 3);
lean_inc_ref(v_F_128_);
v___x_131_ = lp_Multi_T_iter(v_F_128_, v_s3_130_);
v___x_132_ = lean_apply_1(v_F_128_, v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_iter___boxed(lean_object* v_F_133_, lean_object* v_x_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_Multi_T_iter(v_F_133_, v_x_134_);
lean_dec(v_x_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_size(lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(0u);
return v___x_137_;
}
else
{
lean_object* v_s0_138_; lean_object* v_s1_139_; lean_object* v_s2_140_; lean_object* v_s3_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_s0_138_ = lean_ctor_get(v_x_136_, 0);
v_s1_139_ = lean_ctor_get(v_x_136_, 1);
v_s2_140_ = lean_ctor_get(v_x_136_, 2);
v_s3_141_ = lean_ctor_get(v_x_136_, 3);
v___x_142_ = lp_Multi_T_size(v_s0_138_);
v___x_143_ = lp_Multi_T_size(v_s1_139_);
v___x_144_ = lean_nat_add(v___x_142_, v___x_143_);
lean_dec(v___x_143_);
lean_dec(v___x_142_);
v___x_145_ = lp_Multi_T_size(v_s2_140_);
v___x_146_ = lean_nat_add(v___x_144_, v___x_145_);
lean_dec(v___x_145_);
lean_dec(v___x_144_);
v___x_147_ = lp_Multi_T_size(v_s3_141_);
v___x_148_ = lean_nat_add(v___x_146_, v___x_147_);
lean_dec(v___x_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_unsigned_to_nat(1u);
v___x_150_ = lean_nat_add(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_size___boxed(lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = lp_Multi_T_size(v_x_151_);
lean_dec(v_x_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorIdx(lean_object* v_x_153_){
_start:
{
switch(lean_obj_tag(v_x_153_))
{
case 0:
{
lean_object* v___x_154_; 
v___x_154_ = lean_unsigned_to_nat(0u);
return v___x_154_;
}
case 1:
{
lean_object* v___x_155_; 
v___x_155_ = lean_unsigned_to_nat(1u);
return v___x_155_;
}
case 2:
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(2u);
return v___x_156_;
}
default: 
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(3u);
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorIdx___boxed(lean_object* v_x_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = lp_Multi_T_Dom_ctorIdx(v_x_158_);
lean_dec(v_x_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim___redArg(lean_object* v_t_160_, lean_object* v_k_161_){
_start:
{
if (lean_obj_tag(v_t_160_) == 3)
{
lean_object* v_l0_162_; lean_object* v_l1_163_; lean_object* v___x_164_; 
v_l0_162_ = lean_ctor_get(v_t_160_, 0);
lean_inc(v_l0_162_);
v_l1_163_ = lean_ctor_get(v_t_160_, 1);
lean_inc(v_l1_163_);
lean_dec_ref_known(v_t_160_, 2);
v___x_164_ = lean_apply_2(v_k_161_, v_l0_162_, v_l1_163_);
return v___x_164_;
}
else
{
lean_dec(v_t_160_);
return v_k_161_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim(lean_object* v_motive_165_, lean_object* v_ctorIdx_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_k_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_167_, v_k_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim___boxed(lean_object* v_motive_171_, lean_object* v_ctorIdx_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_k_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_Multi_T_Dom_ctorElim(v_motive_171_, v_ctorIdx_172_, v_t_173_, v_h_174_, v_k_175_);
lean_dec(v_ctorIdx_172_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_Zero_elim___redArg(lean_object* v_t_177_, lean_object* v_Zero_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_177_, v_Zero_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_Zero_elim(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_Zero_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_181_, v_Zero_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_One_elim___redArg(lean_object* v_t_185_, lean_object* v_One_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_185_, v_One_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_One_elim(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_One_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_189_, v_One_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03c9_elim___redArg(lean_object* v_t_193_, lean_object* v_00_u03c9_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_193_, v_00_u03c9_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03c9_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_00_u03c9_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_197_, v_00_u03c9_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03a9_elim___redArg(lean_object* v_t_201_, lean_object* v_00_u03a9_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_201_, v_00_u03a9_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03a9_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_00_u03a9_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_205_, v_00_u03a9_207_);
return v___x_208_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_instDecidableEqDom_decEq(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
switch(lean_obj_tag(v_x_209_))
{
case 0:
{
switch(lean_obj_tag(v_x_210_))
{
case 0:
{
uint8_t v___x_211_; 
v___x_211_ = 1;
return v___x_211_;
}
case 3:
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
default: 
{
uint8_t v___x_213_; 
v___x_213_ = 0;
return v___x_213_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_210_))
{
case 1:
{
uint8_t v___x_214_; 
v___x_214_ = 1;
return v___x_214_;
}
case 3:
{
uint8_t v___x_215_; 
v___x_215_ = 0;
return v___x_215_;
}
default: 
{
uint8_t v___x_216_; 
v___x_216_ = 0;
return v___x_216_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_x_210_))
{
case 2:
{
uint8_t v___x_217_; 
v___x_217_ = 1;
return v___x_217_;
}
case 3:
{
uint8_t v___x_218_; 
v___x_218_ = 0;
return v___x_218_;
}
default: 
{
uint8_t v___x_219_; 
v___x_219_ = 0;
return v___x_219_;
}
}
}
default: 
{
lean_object* v_l0_220_; lean_object* v_l1_221_; uint8_t v___x_222_; 
v_l0_220_ = lean_ctor_get(v_x_209_, 0);
v_l1_221_ = lean_ctor_get(v_x_209_, 1);
v___x_222_ = 0;
if (lean_obj_tag(v_x_210_) == 3)
{
lean_object* v_l0_223_; lean_object* v_l1_224_; uint8_t v___x_225_; 
v_l0_223_ = lean_ctor_get(v_x_210_, 0);
v_l1_224_ = lean_ctor_get(v_x_210_, 1);
v___x_225_ = lp_Multi_instDecidableEqT_decEq(v_l0_220_, v_l0_223_);
if (v___x_225_ == 0)
{
return v___x_222_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = lp_Multi_instDecidableEqT_decEq(v_l1_221_, v_l1_224_);
if (v___x_226_ == 0)
{
return v___x_222_;
}
else
{
return v___x_226_;
}
}
}
else
{
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_instDecidableEqDom_decEq___boxed(lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = lp_Multi_T_instDecidableEqDom_decEq(v_x_227_, v_x_228_);
lean_dec(v_x_228_);
lean_dec(v_x_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_instDecidableEqDom(lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lp_Multi_T_instDecidableEqDom_decEq(v_x_231_, v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_instDecidableEqDom___boxed(lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
uint8_t v_res_236_; lean_object* v_r_237_; 
v_res_236_ = lp_Multi_T_instDecidableEqDom(v_x_234_, v_x_235_);
lean_dec(v_x_235_);
lean_dec(v_x_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_dom(lean_object* v_s_238_){
_start:
{
if (lean_obj_tag(v_s_238_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
lean_object* v_s0_240_; lean_object* v_s1_241_; lean_object* v_s2_242_; lean_object* v_s3_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_273_; 
v_s0_240_ = lean_ctor_get(v_s_238_, 0);
v_s1_241_ = lean_ctor_get(v_s_238_, 1);
v_s2_242_ = lean_ctor_get(v_s_238_, 2);
v_s3_243_ = lean_ctor_get(v_s_238_, 3);
v_isSharedCheck_273_ = !lean_is_exclusive(v_s_238_);
if (v_isSharedCheck_273_ == 0)
{
v___x_245_ = v_s_238_;
v_isShared_246_ = v_isSharedCheck_273_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_s3_243_);
lean_inc(v_s2_242_);
lean_inc(v_s1_241_);
lean_inc(v_s0_240_);
lean_dec(v_s_238_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_273_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_box(0);
v___x_248_ = lp_Multi_instDecidableEqT_decEq(v_s3_243_, v___x_247_);
if (v___x_248_ == 0)
{
lean_del_object(v___x_245_);
lean_dec(v_s2_242_);
lean_dec(v_s1_241_);
lean_dec(v_s0_240_);
v_s_238_ = v_s3_243_;
goto _start;
}
else
{
lean_object* v___x_250_; 
lean_dec(v_s3_243_);
lean_inc(v_s2_242_);
v___x_250_ = lp_Multi_T_dom(v_s2_242_);
switch(lean_obj_tag(v___x_250_))
{
case 0:
{
lean_object* v___x_251_; 
lean_dec(v_s2_242_);
lean_inc(v_s1_241_);
v___x_251_ = lp_Multi_T_dom(v_s1_241_);
switch(lean_obj_tag(v___x_251_))
{
case 0:
{
lean_object* v___x_252_; 
lean_del_object(v___x_245_);
lean_dec(v_s1_241_);
lean_inc(v_s0_240_);
v___x_252_ = lp_Multi_T_dom(v_s0_240_);
switch(lean_obj_tag(v___x_252_))
{
case 0:
{
lean_object* v___x_253_; 
lean_dec(v_s0_240_);
v___x_253_ = lean_box(1);
return v___x_253_;
}
case 1:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_254_, 0, v_s0_240_);
lean_ctor_set(v___x_254_, 1, v___x_247_);
return v___x_254_;
}
default: 
{
lean_dec(v_s0_240_);
return v___x_252_;
}
}
}
case 1:
{
lean_object* v___x_255_; 
lean_del_object(v___x_245_);
v___x_255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_255_, 0, v_s0_240_);
lean_ctor_set(v___x_255_, 1, v_s1_241_);
return v___x_255_;
}
case 2:
{
lean_del_object(v___x_245_);
lean_dec(v_s1_241_);
lean_dec(v_s0_240_);
return v___x_251_;
}
default: 
{
lean_object* v_l0_256_; lean_object* v_l1_257_; lean_object* v___x_259_; 
v_l0_256_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_l0_256_);
v_l1_257_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_l1_257_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 3, v___x_247_);
lean_ctor_set(v___x_245_, 2, v___x_247_);
v___x_259_ = v___x_245_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_s0_240_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_s1_241_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v___x_247_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_260_, 0, v_l0_256_);
lean_ctor_set(v___x_260_, 1, v_l1_257_);
lean_ctor_set(v___x_260_, 2, v___x_247_);
lean_ctor_set(v___x_260_, 3, v___x_247_);
v___x_261_ = lp_Multi_T_decLt(v___x_259_, v___x_260_);
lean_dec_ref_known(v___x_260_, 4);
lean_dec_ref(v___x_259_);
if (v___x_261_ == 0)
{
return v___x_251_;
}
else
{
lean_object* v___x_262_; 
lean_dec_ref_known(v___x_251_, 2);
v___x_262_ = lean_box(2);
return v___x_262_;
}
}
}
}
}
case 1:
{
lean_object* v___x_264_; 
lean_del_object(v___x_245_);
lean_dec(v_s2_242_);
lean_dec(v_s1_241_);
lean_dec(v_s0_240_);
v___x_264_ = lean_box(2);
return v___x_264_;
}
case 2:
{
lean_del_object(v___x_245_);
lean_dec(v_s2_242_);
lean_dec(v_s1_241_);
lean_dec(v_s0_240_);
return v___x_250_;
}
default: 
{
lean_object* v_l0_265_; lean_object* v_l1_266_; lean_object* v___x_268_; 
v_l0_265_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_l0_265_);
v_l1_266_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_l1_266_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 3, v___x_247_);
v___x_268_ = v___x_245_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_s0_240_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_s1_241_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_s2_242_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v___x_247_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_269_, 0, v_l0_265_);
lean_ctor_set(v___x_269_, 1, v_l1_266_);
lean_ctor_set(v___x_269_, 2, v___x_247_);
lean_ctor_set(v___x_269_, 3, v___x_247_);
v___x_270_ = lp_Multi_T_decLt(v___x_268_, v___x_269_);
lean_dec_ref_known(v___x_269_, 4);
lean_dec_ref(v___x_268_);
if (v___x_270_ == 0)
{
return v___x_250_;
}
else
{
lean_object* v___x_271_; 
lean_dec_ref_known(v___x_250_, 2);
v___x_271_ = lean_box(2);
return v___x_271_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_iter_match__1_splitter___redArg(lean_object* v_x_274_, lean_object* v_h__1_275_, lean_object* v_h__2_276_){
_start:
{
if (lean_obj_tag(v_x_274_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec(v_h__2_276_);
v___x_277_ = lean_box(0);
v___x_278_ = lean_apply_1(v_h__1_275_, v___x_277_);
return v___x_278_;
}
else
{
lean_object* v_s0_279_; lean_object* v_s1_280_; lean_object* v_s2_281_; lean_object* v_s3_282_; lean_object* v___x_283_; 
lean_dec(v_h__1_275_);
v_s0_279_ = lean_ctor_get(v_x_274_, 0);
lean_inc(v_s0_279_);
v_s1_280_ = lean_ctor_get(v_x_274_, 1);
lean_inc(v_s1_280_);
v_s2_281_ = lean_ctor_get(v_x_274_, 2);
lean_inc(v_s2_281_);
v_s3_282_ = lean_ctor_get(v_x_274_, 3);
lean_inc(v_s3_282_);
lean_dec_ref_known(v_x_274_, 4);
v___x_283_ = lean_apply_4(v_h__2_276_, v_s0_279_, v_s1_280_, v_s2_281_, v_s3_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_iter_match__1_splitter(lean_object* v_motive_284_, lean_object* v_x_285_, lean_object* v_h__1_286_, lean_object* v_h__2_287_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v_h__2_287_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_apply_1(v_h__1_286_, v___x_288_);
return v___x_289_;
}
else
{
lean_object* v_s0_290_; lean_object* v_s1_291_; lean_object* v_s2_292_; lean_object* v_s3_293_; lean_object* v___x_294_; 
lean_dec(v_h__1_286_);
v_s0_290_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_s0_290_);
v_s1_291_ = lean_ctor_get(v_x_285_, 1);
lean_inc(v_s1_291_);
v_s2_292_ = lean_ctor_get(v_x_285_, 2);
lean_inc(v_s2_292_);
v_s3_293_ = lean_ctor_get(v_x_285_, 3);
lean_inc(v_s3_293_);
lean_dec_ref_known(v_x_285_, 4);
v___x_294_ = lean_apply_4(v_h__2_287_, v_s0_290_, v_s1_291_, v_s2_292_, v_s3_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_dom_match__1_splitter___redArg(lean_object* v_x_295_, lean_object* v_h__1_296_, lean_object* v_h__2_297_, lean_object* v_h__3_298_, lean_object* v_h__4_299_){
_start:
{
switch(lean_obj_tag(v_x_295_))
{
case 0:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_h__4_299_);
lean_dec(v_h__3_298_);
lean_dec(v_h__2_297_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__1_296_, v___x_300_);
return v___x_301_;
}
case 1:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_h__4_299_);
lean_dec(v_h__3_298_);
lean_dec(v_h__1_296_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_1(v_h__2_297_, v___x_302_);
return v___x_303_;
}
case 2:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec(v_h__4_299_);
lean_dec(v_h__2_297_);
lean_dec(v_h__1_296_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_h__3_298_, v___x_304_);
return v___x_305_;
}
default: 
{
lean_object* v_l0_306_; lean_object* v_l1_307_; lean_object* v___x_308_; 
lean_dec(v_h__3_298_);
lean_dec(v_h__2_297_);
lean_dec(v_h__1_296_);
v_l0_306_ = lean_ctor_get(v_x_295_, 0);
lean_inc(v_l0_306_);
v_l1_307_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_l1_307_);
lean_dec_ref_known(v_x_295_, 2);
v___x_308_ = lean_apply_2(v_h__4_299_, v_l0_306_, v_l1_307_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_dom_match__1_splitter(lean_object* v_motive_309_, lean_object* v_x_310_, lean_object* v_h__1_311_, lean_object* v_h__2_312_, lean_object* v_h__3_313_, lean_object* v_h__4_314_){
_start:
{
switch(lean_obj_tag(v_x_310_))
{
case 0:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_h__4_314_);
lean_dec(v_h__3_313_);
lean_dec(v_h__2_312_);
v___x_315_ = lean_box(0);
v___x_316_ = lean_apply_1(v_h__1_311_, v___x_315_);
return v___x_316_;
}
case 1:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v_h__4_314_);
lean_dec(v_h__3_313_);
lean_dec(v_h__1_311_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_apply_1(v_h__2_312_, v___x_317_);
return v___x_318_;
}
case 2:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_h__4_314_);
lean_dec(v_h__2_312_);
lean_dec(v_h__1_311_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_1(v_h__3_313_, v___x_319_);
return v___x_320_;
}
default: 
{
lean_object* v_l0_321_; lean_object* v_l1_322_; lean_object* v___x_323_; 
lean_dec(v_h__3_313_);
lean_dec(v_h__2_312_);
lean_dec(v_h__1_311_);
v_l0_321_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_l0_321_);
v_l1_322_ = lean_ctor_get(v_x_310_, 1);
lean_inc(v_l1_322_);
lean_dec_ref_known(v_x_310_, 2);
v___x_323_ = lean_apply_2(v_h__4_314_, v_l0_321_, v_l1_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0___boxed(lean_object* v_s1_324_, lean_object* v_f_x27_325_, lean_object* v___x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = lp_Multi_T_fund___lam__0(v_s1_324_, v_f_x27_325_, v___x_326_, v_x_327_);
lean_dec(v_x_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__1(lean_object* v_s1_329_, lean_object* v_l0_330_, lean_object* v_e_x27_331_, lean_object* v___x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lp_Multi_T_fund(v_s1_329_, v_x_333_);
v___x_335_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_335_, 0, v_l0_330_);
lean_ctor_set(v___x_335_, 1, v_e_x27_331_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
lean_ctor_set(v___x_335_, 3, v___x_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__1___boxed(lean_object* v_s1_336_, lean_object* v_l0_337_, lean_object* v_e_x27_338_, lean_object* v___x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = lp_Multi_T_fund___lam__1(v_s1_336_, v_l0_337_, v_e_x27_338_, v___x_339_, v_x_340_);
lean_dec(v_x_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__2(lean_object* v_s2_342_, lean_object* v_f_x27_343_, lean_object* v___x_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lp_Multi_T_fund(v_s2_342_, v_x_345_);
lean_inc(v___x_344_);
v___x_347_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_347_, 0, v_f_x27_343_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
lean_ctor_set(v___x_347_, 2, v___x_344_);
lean_ctor_set(v___x_347_, 3, v___x_344_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__2___boxed(lean_object* v_s2_348_, lean_object* v_f_x27_349_, lean_object* v___x_350_, lean_object* v_x_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = lp_Multi_T_fund___lam__2(v_s2_348_, v_f_x27_349_, v___x_350_, v_x_351_);
lean_dec(v_x_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__3(lean_object* v_s2_353_, lean_object* v_l0_354_, lean_object* v_e_x27_355_, lean_object* v___x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lp_Multi_T_fund(v_s2_353_, v_x_357_);
v___x_359_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_359_, 0, v_l0_354_);
lean_ctor_set(v___x_359_, 1, v_e_x27_355_);
lean_ctor_set(v___x_359_, 2, v___x_358_);
lean_ctor_set(v___x_359_, 3, v___x_356_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__3___boxed(lean_object* v_s2_360_, lean_object* v_l0_361_, lean_object* v_e_x27_362_, lean_object* v___x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = lp_Multi_T_fund___lam__3(v_s2_360_, v_l0_361_, v_e_x27_362_, v___x_363_, v_x_364_);
lean_dec(v_x_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund(lean_object* v_s_366_, lean_object* v_t_367_){
_start:
{
if (lean_obj_tag(v_s_366_) == 0)
{
return v_s_366_;
}
else
{
lean_object* v_s0_368_; lean_object* v_s1_369_; lean_object* v_s2_370_; lean_object* v_s3_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_445_; 
v_s0_368_ = lean_ctor_get(v_s_366_, 0);
v_s1_369_ = lean_ctor_get(v_s_366_, 1);
v_s2_370_ = lean_ctor_get(v_s_366_, 2);
v_s3_371_ = lean_ctor_get(v_s_366_, 3);
v_isSharedCheck_445_ = !lean_is_exclusive(v_s_366_);
if (v_isSharedCheck_445_ == 0)
{
v___x_373_ = v_s_366_;
v_isShared_374_ = v_isSharedCheck_445_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_s3_371_);
lean_inc(v_s2_370_);
lean_inc(v_s1_369_);
lean_inc(v_s0_368_);
lean_dec(v_s_366_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_445_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = lean_box(0);
v___x_376_ = lp_Multi_instDecidableEqT_decEq(v_s3_371_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lp_Multi_T_fund(v_s3_371_, v_t_367_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_377_);
v___x_379_ = v___x_373_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_s0_368_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_s1_369_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_s2_370_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_object* v___x_381_; 
lean_dec(v_s3_371_);
lean_inc(v_s2_370_);
v___x_381_ = lp_Multi_T_dom(v_s2_370_);
switch(lean_obj_tag(v___x_381_))
{
case 0:
{
lean_object* v___x_382_; 
lean_dec(v_s2_370_);
lean_inc(v_s1_369_);
v___x_382_ = lp_Multi_T_dom(v_s1_369_);
switch(lean_obj_tag(v___x_382_))
{
case 0:
{
lean_object* v___x_383_; 
lean_dec(v_s1_369_);
lean_inc(v_s0_368_);
v___x_383_ = lp_Multi_T_dom(v_s0_368_);
switch(lean_obj_tag(v___x_383_))
{
case 0:
{
lean_del_object(v___x_373_);
lean_dec(v_s0_368_);
return v___x_375_;
}
case 1:
{
lean_del_object(v___x_373_);
lean_dec(v_s0_368_);
lean_inc(v_t_367_);
return v_t_367_;
}
default: 
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec(v___x_383_);
v___x_384_ = lp_Multi_T_fund(v_s0_368_, v_t_367_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_375_);
lean_ctor_set(v___x_373_, 2, v___x_375_);
lean_ctor_set(v___x_373_, 1, v___x_375_);
lean_ctor_set(v___x_373_, 0, v___x_384_);
v___x_386_ = v___x_373_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v___x_375_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
case 1:
{
lean_del_object(v___x_373_);
lean_dec(v_s1_369_);
lean_dec(v_s0_368_);
lean_inc(v_t_367_);
return v_t_367_;
}
case 2:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lp_Multi_T_fund(v_s1_369_, v_t_367_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_375_);
lean_ctor_set(v___x_373_, 2, v___x_375_);
lean_ctor_set(v___x_373_, 1, v___x_388_);
v___x_390_ = v___x_373_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_s0_368_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_391_, 3, v___x_375_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
default: 
{
lean_object* v_l0_392_; lean_object* v_l1_393_; lean_object* v___x_395_; 
v_l0_392_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_l0_392_);
v_l1_393_ = lean_ctor_get(v___x_382_, 1);
lean_inc(v_l1_393_);
lean_dec_ref_known(v___x_382_, 2);
lean_inc(v_s1_369_);
lean_inc(v_s0_368_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_375_);
lean_ctor_set(v___x_373_, 2, v___x_375_);
v___x_395_ = v___x_373_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_s0_368_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_s1_369_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v___x_375_);
v___x_395_ = v_reuseFailAlloc_413_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; uint8_t v___x_397_; 
lean_inc(v_l1_393_);
lean_inc(v_l0_392_);
v___x_396_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_396_, 0, v_l0_392_);
lean_ctor_set(v___x_396_, 1, v_l1_393_);
lean_ctor_set(v___x_396_, 2, v___x_375_);
lean_ctor_set(v___x_396_, 3, v___x_375_);
v___x_397_ = lp_Multi_T_decLt(v___x_395_, v___x_396_);
lean_dec_ref_known(v___x_396_, 4);
lean_dec_ref(v___x_395_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_l1_393_);
lean_dec(v_l0_392_);
v___x_398_ = lp_Multi_T_fund(v_s1_369_, v_t_367_);
v___x_399_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_399_, 0, v_s0_368_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_ctor_set(v___x_399_, 2, v___x_375_);
lean_ctor_set(v___x_399_, 3, v___x_375_);
return v___x_399_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
lean_inc(v_l1_393_);
v___x_400_ = lp_Multi_T_dom(v_l1_393_);
v___x_401_ = lean_box(1);
v___x_402_ = lp_Multi_T_instDecidableEqDom_decEq(v___x_400_, v___x_401_);
lean_dec(v___x_400_);
if (v___x_402_ == 0)
{
lean_object* v_f_x27_403_; lean_object* v_F_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_l1_393_);
v_f_x27_403_ = lp_Multi_T_fund(v_l0_392_, v___x_375_);
lean_inc(v_s1_369_);
v_F_404_ = lean_alloc_closure((void*)(lp_Multi_T_fund___lam__0___boxed), 4, 3);
lean_closure_set(v_F_404_, 0, v_s1_369_);
lean_closure_set(v_F_404_, 1, v_f_x27_403_);
lean_closure_set(v_F_404_, 2, v___x_375_);
v___x_405_ = lp_Multi_T_iter(v_F_404_, v_t_367_);
v___x_406_ = lp_Multi_T_fund(v_s1_369_, v___x_405_);
lean_dec(v___x_405_);
v___x_407_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_407_, 0, v_s0_368_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_375_);
lean_ctor_set(v___x_407_, 3, v___x_375_);
return v___x_407_;
}
else
{
lean_object* v_e_x27_408_; lean_object* v_F_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_e_x27_408_ = lp_Multi_T_fund(v_l1_393_, v___x_375_);
lean_inc(v_s1_369_);
v_F_409_ = lean_alloc_closure((void*)(lp_Multi_T_fund___lam__1___boxed), 5, 4);
lean_closure_set(v_F_409_, 0, v_s1_369_);
lean_closure_set(v_F_409_, 1, v_l0_392_);
lean_closure_set(v_F_409_, 2, v_e_x27_408_);
lean_closure_set(v_F_409_, 3, v___x_375_);
v___x_410_ = lp_Multi_T_iter(v_F_409_, v_t_367_);
v___x_411_ = lp_Multi_T_fund(v_s1_369_, v___x_410_);
lean_dec(v___x_410_);
v___x_412_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_412_, 0, v_s0_368_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_375_);
lean_ctor_set(v___x_412_, 3, v___x_375_);
return v___x_412_;
}
}
}
}
}
}
case 1:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lp_Multi_T_fund(v_s2_370_, v___x_375_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_375_);
lean_ctor_set(v___x_373_, 2, v___x_414_);
v___x_416_ = v___x_373_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_s0_368_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_s1_369_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v___x_375_);
v___x_416_ = v_reuseFailAlloc_418_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; 
v___x_417_ = lp_Multi_T_mul(v___x_416_, v_t_367_);
lean_dec_ref(v___x_416_);
return v___x_417_;
}
}
case 2:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_419_ = lp_Multi_T_fund(v_s2_370_, v_t_367_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_375_);
lean_ctor_set(v___x_373_, 2, v___x_419_);
v___x_421_ = v___x_373_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_s0_368_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_s1_369_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v___x_375_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
default: 
{
lean_object* v_l0_423_; lean_object* v_l1_424_; lean_object* v___x_426_; 
v_l0_423_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_l0_423_);
v_l1_424_ = lean_ctor_get(v___x_381_, 1);
lean_inc(v_l1_424_);
lean_dec_ref_known(v___x_381_, 2);
lean_inc(v_s2_370_);
lean_inc(v_s1_369_);
lean_inc(v_s0_368_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 3, v___x_375_);
v___x_426_ = v___x_373_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_s0_368_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_s1_369_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_s2_370_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v___x_375_);
v___x_426_ = v_reuseFailAlloc_444_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
lean_inc(v_l1_424_);
lean_inc(v_l0_423_);
v___x_427_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_427_, 0, v_l0_423_);
lean_ctor_set(v___x_427_, 1, v_l1_424_);
lean_ctor_set(v___x_427_, 2, v___x_375_);
lean_ctor_set(v___x_427_, 3, v___x_375_);
v___x_428_ = lp_Multi_T_decLt(v___x_426_, v___x_427_);
lean_dec_ref_known(v___x_427_, 4);
lean_dec_ref(v___x_426_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_l1_424_);
lean_dec(v_l0_423_);
v___x_429_ = lp_Multi_T_fund(v_s2_370_, v_t_367_);
v___x_430_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_430_, 0, v_s0_368_);
lean_ctor_set(v___x_430_, 1, v_s1_369_);
lean_ctor_set(v___x_430_, 2, v___x_429_);
lean_ctor_set(v___x_430_, 3, v___x_375_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
lean_inc(v_l1_424_);
v___x_431_ = lp_Multi_T_dom(v_l1_424_);
v___x_432_ = lean_box(1);
v___x_433_ = lp_Multi_T_instDecidableEqDom_decEq(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
if (v___x_433_ == 0)
{
lean_object* v_f_x27_434_; lean_object* v_F_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v_l1_424_);
v_f_x27_434_ = lp_Multi_T_fund(v_l0_423_, v___x_375_);
lean_inc(v_s2_370_);
v_F_435_ = lean_alloc_closure((void*)(lp_Multi_T_fund___lam__2___boxed), 4, 3);
lean_closure_set(v_F_435_, 0, v_s2_370_);
lean_closure_set(v_F_435_, 1, v_f_x27_434_);
lean_closure_set(v_F_435_, 2, v___x_375_);
v___x_436_ = lp_Multi_T_iter(v_F_435_, v_t_367_);
v___x_437_ = lp_Multi_T_fund(v_s2_370_, v___x_436_);
lean_dec(v___x_436_);
v___x_438_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_438_, 0, v_s0_368_);
lean_ctor_set(v___x_438_, 1, v_s1_369_);
lean_ctor_set(v___x_438_, 2, v___x_437_);
lean_ctor_set(v___x_438_, 3, v___x_375_);
return v___x_438_;
}
else
{
lean_object* v_e_x27_439_; lean_object* v_F_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_e_x27_439_ = lp_Multi_T_fund(v_l1_424_, v___x_375_);
lean_inc(v_s2_370_);
v_F_440_ = lean_alloc_closure((void*)(lp_Multi_T_fund___lam__3___boxed), 5, 4);
lean_closure_set(v_F_440_, 0, v_s2_370_);
lean_closure_set(v_F_440_, 1, v_l0_423_);
lean_closure_set(v_F_440_, 2, v_e_x27_439_);
lean_closure_set(v_F_440_, 3, v___x_375_);
v___x_441_ = lp_Multi_T_iter(v_F_440_, v_t_367_);
v___x_442_ = lp_Multi_T_fund(v_s2_370_, v___x_441_);
lean_dec(v___x_441_);
v___x_443_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_443_, 0, v_s0_368_);
lean_ctor_set(v___x_443_, 1, v_s1_369_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_ctor_set(v___x_443_, 3, v___x_375_);
return v___x_443_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0(lean_object* v_s1_446_, lean_object* v_f_x27_447_, lean_object* v___x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lp_Multi_T_fund(v_s1_446_, v_x_449_);
lean_inc(v___x_448_);
v___x_451_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_451_, 0, v_f_x27_447_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_ctor_set(v___x_451_, 2, v___x_448_);
lean_ctor_set(v___x_451_, 3, v___x_448_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___boxed(lean_object* v_s_452_, lean_object* v_t_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = lp_Multi_T_fund(v_s_452_, v_t_453_);
lean_dec(v_t_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_fund_match__1_splitter___redArg(lean_object* v_x_455_, lean_object* v_h__1_456_, lean_object* v_h__2_457_, lean_object* v_h__3_458_, lean_object* v_h__4_459_){
_start:
{
switch(lean_obj_tag(v_x_455_))
{
case 0:
{
lean_object* v___x_460_; 
lean_dec(v_h__4_459_);
lean_dec(v_h__3_458_);
lean_dec(v_h__2_457_);
v___x_460_ = lean_apply_1(v_h__1_456_, lean_box(0));
return v___x_460_;
}
case 1:
{
lean_object* v___x_461_; 
lean_dec(v_h__4_459_);
lean_dec(v_h__3_458_);
lean_dec(v_h__1_456_);
v___x_461_ = lean_apply_1(v_h__2_457_, lean_box(0));
return v___x_461_;
}
case 2:
{
lean_object* v___x_462_; 
lean_dec(v_h__4_459_);
lean_dec(v_h__2_457_);
lean_dec(v_h__1_456_);
v___x_462_ = lean_apply_1(v_h__3_458_, lean_box(0));
return v___x_462_;
}
default: 
{
lean_object* v_l0_463_; lean_object* v_l1_464_; lean_object* v___x_465_; 
lean_dec(v_h__3_458_);
lean_dec(v_h__2_457_);
lean_dec(v_h__1_456_);
v_l0_463_ = lean_ctor_get(v_x_455_, 0);
lean_inc(v_l0_463_);
v_l1_464_ = lean_ctor_get(v_x_455_, 1);
lean_inc(v_l1_464_);
lean_dec_ref_known(v_x_455_, 2);
v___x_465_ = lean_apply_3(v_h__4_459_, v_l0_463_, v_l1_464_, lean_box(0));
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term3_0__T_fund_match__1_splitter(lean_object* v_motive_466_, lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_, lean_object* v_h__3_470_, lean_object* v_h__4_471_){
_start:
{
switch(lean_obj_tag(v_x_467_))
{
case 0:
{
lean_object* v___x_472_; 
lean_dec(v_h__4_471_);
lean_dec(v_h__3_470_);
lean_dec(v_h__2_469_);
v___x_472_ = lean_apply_1(v_h__1_468_, lean_box(0));
return v___x_472_;
}
case 1:
{
lean_object* v___x_473_; 
lean_dec(v_h__4_471_);
lean_dec(v_h__3_470_);
lean_dec(v_h__1_468_);
v___x_473_ = lean_apply_1(v_h__2_469_, lean_box(0));
return v___x_473_;
}
case 2:
{
lean_object* v___x_474_; 
lean_dec(v_h__4_471_);
lean_dec(v_h__2_469_);
lean_dec(v_h__1_468_);
v___x_474_ = lean_apply_1(v_h__3_470_, lean_box(0));
return v___x_474_;
}
default: 
{
lean_object* v_l0_475_; lean_object* v_l1_476_; lean_object* v___x_477_; 
lean_dec(v_h__3_470_);
lean_dec(v_h__2_469_);
lean_dec(v_h__1_468_);
v_l0_475_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_l0_475_);
v_l1_476_ = lean_ctor_get(v_x_467_, 1);
lean_inc(v_l1_476_);
lean_dec_ref_known(v_x_467_, 2);
v___x_477_ = lean_apply_3(v_h__4_471_, v_l0_475_, v_l1_476_, lean_box(0));
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_LF(lean_object* v_n_478_){
_start:
{
lean_object* v_zero_479_; uint8_t v_isZero_480_; 
v_zero_479_ = lean_unsigned_to_nat(0u);
v_isZero_480_ = lean_nat_dec_eq(v_n_478_, v_zero_479_);
if (v_isZero_480_ == 1)
{
lean_object* v___x_481_; 
v___x_481_ = lean_box(0);
return v___x_481_;
}
else
{
lean_object* v_one_482_; lean_object* v_n_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_one_482_ = lean_unsigned_to_nat(1u);
v_n_483_ = lean_nat_sub(v_n_478_, v_one_482_);
v___x_484_ = lp_Multi_T_LF(v_n_483_);
lean_dec(v_n_483_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
lean_ctor_set(v___x_486_, 2, v___x_485_);
lean_ctor_set(v___x_486_, 3, v___x_485_);
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_LF___boxed(lean_object* v_n_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = lp_Multi_T_LF(v_n_487_);
lean_dec(v_n_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ofNat(lean_object* v_x_489_){
_start:
{
lean_object* v_zero_490_; uint8_t v_isZero_491_; 
v_zero_490_ = lean_unsigned_to_nat(0u);
v_isZero_491_ = lean_nat_dec_eq(v_x_489_, v_zero_490_);
if (v_isZero_491_ == 1)
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(0);
return v___x_492_;
}
else
{
lean_object* v_one_493_; lean_object* v_n_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_one_493_ = lean_unsigned_to_nat(1u);
v_n_494_ = lean_nat_sub(v_x_489_, v_one_493_);
v___x_495_ = lean_box(0);
v___x_496_ = lp_Multi_T_ofNat(v_n_494_);
lean_dec(v_n_494_);
v___x_497_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
lean_ctor_set(v___x_497_, 2, v___x_495_);
lean_ctor_set(v___x_497_, 3, v___x_496_);
return v___x_497_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ofNat___boxed(lean_object* v_x_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = lp_Multi_T_ofNat(v_x_498_);
lean_dec(v_x_498_);
return v_res_499_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_order(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_Term3(uint8_t builtin) {
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
res = initialize_Multi_Multi_order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Multi_instLTT = _init_lp_Multi_instLTT();
lean_mark_persistent(lp_Multi_instLTT);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
