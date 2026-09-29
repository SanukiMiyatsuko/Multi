// Lean compiler output
// Module: Multi.Term2Syntax
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
uint8_t lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_Multi_T_dom___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_iter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_iter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_dom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_dom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_fund___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_fund_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_fund_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_head(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_G(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_LF(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_LF___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_mul_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_mul_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_s0_8_; lean_object* v_s1_9_; lean_object* v_s2_10_; lean_object* v___x_11_; 
v_s0_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_s0_8_);
v_s1_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_s1_9_);
v_s2_10_ = lean_ctor_get(v_t_6_, 2);
lean_inc(v_s2_10_);
lean_dec_ref_known(v_t_6_, 3);
v___x_11_ = lean_apply_3(v_k_7_, v_s0_8_, v_s1_9_, v_s2_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_Multi_T_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_Multi_T_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Z_elim___redArg(lean_object* v_t_24_, lean_object* v_Z_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_Multi_T_ctorElim___redArg(v_t_24_, v_Z_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Z_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_Z_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_Multi_T_ctorElim___redArg(v_t_28_, v_Z_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_P_elim___redArg(lean_object* v_t_32_, lean_object* v_P_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_Multi_T_ctorElim___redArg(v_t_32_, v_P_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_P_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_P_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_Multi_T_ctorElim___redArg(v_t_36_, v_P_38_);
return v___x_39_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableEqT_decEq(lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_40_) == 0)
{
if (lean_obj_tag(v_x_41_) == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 1;
return v___x_42_;
}
else
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
}
else
{
lean_object* v_s0_44_; lean_object* v_s1_45_; lean_object* v_s2_46_; uint8_t v___x_47_; 
v_s0_44_ = lean_ctor_get(v_x_40_, 0);
v_s1_45_ = lean_ctor_get(v_x_40_, 1);
v_s2_46_ = lean_ctor_get(v_x_40_, 2);
v___x_47_ = 0;
if (lean_obj_tag(v_x_41_) == 0)
{
return v___x_47_;
}
else
{
lean_object* v_s0_48_; lean_object* v_s1_49_; lean_object* v_s2_50_; uint8_t v_inst_51_; 
v_s0_48_ = lean_ctor_get(v_x_41_, 0);
v_s1_49_ = lean_ctor_get(v_x_41_, 1);
v_s2_50_ = lean_ctor_get(v_x_41_, 2);
v_inst_51_ = lp_Multi_instDecidableEqT_decEq(v_s0_44_, v_s0_48_);
if (v_inst_51_ == 0)
{
return v___x_47_;
}
else
{
uint8_t v_inst_52_; 
v_inst_52_ = lp_Multi_instDecidableEqT_decEq(v_s1_45_, v_s1_49_);
if (v_inst_52_ == 0)
{
return v___x_47_;
}
else
{
uint8_t v_inst_53_; 
v_inst_53_ = lp_Multi_instDecidableEqT_decEq(v_s2_46_, v_s2_50_);
if (v_inst_53_ == 0)
{
return v___x_47_;
}
else
{
return v_inst_53_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableEqT_decEq___boxed(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = lp_Multi_instDecidableEqT_decEq(v_x_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec(v_x_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableEqT(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lp_Multi_instDecidableEqT_decEq(v_x_58_, v_x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableEqT___boxed(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = lp_Multi_instDecidableEqT(v_x_61_, v_x_62_);
lean_dec(v_x_62_);
lean_dec(v_x_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
static lean_object* _init_lp_Multi_instLTT(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_decLt(lean_object* v_a_66_, lean_object* v_b_67_){
_start:
{
if (lean_obj_tag(v_a_66_) == 0)
{
if (lean_obj_tag(v_b_67_) == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 1;
return v___x_69_;
}
}
else
{
lean_object* v_s0_70_; lean_object* v_s1_71_; lean_object* v_s2_72_; uint8_t v___x_73_; 
v_s0_70_ = lean_ctor_get(v_a_66_, 0);
v_s1_71_ = lean_ctor_get(v_a_66_, 1);
v_s2_72_ = lean_ctor_get(v_a_66_, 2);
v___x_73_ = 0;
if (lean_obj_tag(v_b_67_) == 0)
{
return v___x_73_;
}
else
{
lean_object* v_s0_74_; lean_object* v_s1_75_; lean_object* v_s2_76_; uint8_t v___x_77_; uint8_t v___x_78_; 
v_s0_74_ = lean_ctor_get(v_b_67_, 0);
v_s1_75_ = lean_ctor_get(v_b_67_, 1);
v_s2_76_ = lean_ctor_get(v_b_67_, 2);
v___x_77_ = lp_Multi_instDecidableEqT_decEq(v_s0_70_, v_s0_74_);
v___x_78_ = lp_Multi_T_decLt(v_s0_70_, v_s0_74_);
if (v___x_78_ == 0)
{
if (v___x_77_ == 0)
{
return v___x_73_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = lp_Multi_T_decLt(v_s1_71_, v_s1_75_);
if (v___x_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = lp_Multi_instDecidableEqT_decEq(v_s1_71_, v_s1_75_);
if (v___x_80_ == 0)
{
return v___x_73_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = lp_Multi_T_decLt(v_s2_72_, v_s2_76_);
if (v___x_81_ == 0)
{
return v___x_73_;
}
else
{
return v___x_81_;
}
}
}
else
{
return v___x_79_;
}
}
}
else
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_decLt___boxed(lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = lp_Multi_T_decLt(v_a_82_, v_b_83_);
lean_dec(v_b_83_);
lean_dec(v_a_82_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableLtT(lean_object* v_a_86_, lean_object* v_b_87_){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = lp_Multi_T_decLt(v_a_86_, v_b_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableLtT___boxed(lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = lp_Multi_instDecidableLtT(v_a_89_, v_b_90_);
lean_dec(v_b_90_);
lean_dec(v_a_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_add(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
lean_inc(v_x_94_);
return v_x_94_;
}
else
{
if (lean_obj_tag(v_x_94_) == 0)
{
return v_x_93_;
}
else
{
lean_object* v_s0_95_; lean_object* v_s1_96_; lean_object* v_s2_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_105_; 
v_s0_95_ = lean_ctor_get(v_x_93_, 0);
v_s1_96_ = lean_ctor_get(v_x_93_, 1);
v_s2_97_ = lean_ctor_get(v_x_93_, 2);
v_isSharedCheck_105_ = !lean_is_exclusive(v_x_93_);
if (v_isSharedCheck_105_ == 0)
{
v___x_99_ = v_x_93_;
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_s2_97_);
lean_inc(v_s1_96_);
lean_inc(v_s0_95_);
lean_dec(v_x_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_105_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lp_Multi_T_add(v_s2_97_, v_x_94_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 2, v___x_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_s0_95_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_s1_96_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_add___boxed(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_Multi_T_add(v_x_106_, v_x_107_);
lean_dec(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_mul(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
return v_x_112_;
}
else
{
lean_object* v_s2_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_s2_113_ = lean_ctor_get(v_x_112_, 2);
v___x_114_ = lp_Multi_T_mul(v_x_111_, v_s2_113_);
v___x_115_ = lp_Multi_T_add(v___x_114_, v_x_111_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_mul___boxed(lean_object* v_x_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = lp_Multi_T_mul(v_x_116_, v_x_117_);
lean_dec(v_x_117_);
lean_dec(v_x_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_iter(lean_object* v_F_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_dec_ref(v_F_119_);
return v_x_120_;
}
else
{
lean_object* v_s2_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_s2_121_ = lean_ctor_get(v_x_120_, 2);
lean_inc_ref(v_F_119_);
v___x_122_ = lp_Multi_T_iter(v_F_119_, v_s2_121_);
v___x_123_ = lean_apply_1(v_F_119_, v___x_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_iter___boxed(lean_object* v_F_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_Multi_T_iter(v_F_124_, v_x_125_);
lean_dec(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_size(lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_unsigned_to_nat(0u);
return v___x_128_;
}
else
{
lean_object* v_s0_129_; lean_object* v_s1_130_; lean_object* v_s2_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_s0_129_ = lean_ctor_get(v_x_127_, 0);
v_s1_130_ = lean_ctor_get(v_x_127_, 1);
v_s2_131_ = lean_ctor_get(v_x_127_, 2);
v___x_132_ = lp_Multi_T_size(v_s0_129_);
v___x_133_ = lp_Multi_T_size(v_s1_130_);
v___x_134_ = lean_nat_add(v___x_132_, v___x_133_);
lean_dec(v___x_133_);
lean_dec(v___x_132_);
v___x_135_ = lp_Multi_T_size(v_s2_131_);
v___x_136_ = lean_nat_add(v___x_134_, v___x_135_);
lean_dec(v___x_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v___x_136_, v___x_137_);
lean_dec(v___x_136_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_size___boxed(lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_Multi_T_size(v_x_139_);
lean_dec(v_x_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorIdx(lean_object* v_x_141_){
_start:
{
switch(lean_obj_tag(v_x_141_))
{
case 0:
{
lean_object* v___x_142_; 
v___x_142_ = lean_unsigned_to_nat(0u);
return v___x_142_;
}
case 1:
{
lean_object* v___x_143_; 
v___x_143_ = lean_unsigned_to_nat(1u);
return v___x_143_;
}
case 2:
{
lean_object* v___x_144_; 
v___x_144_ = lean_unsigned_to_nat(2u);
return v___x_144_;
}
default: 
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(3u);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorIdx___boxed(lean_object* v_x_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = lp_Multi_T_Dom_ctorIdx(v_x_146_);
lean_dec(v_x_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim___redArg(lean_object* v_t_148_, lean_object* v_k_149_){
_start:
{
if (lean_obj_tag(v_t_148_) == 3)
{
lean_object* v_l0_150_; lean_object* v___x_151_; 
v_l0_150_ = lean_ctor_get(v_t_148_, 0);
lean_inc(v_l0_150_);
lean_dec_ref_known(v_t_148_, 1);
v___x_151_ = lean_apply_1(v_k_149_, v_l0_150_);
return v___x_151_;
}
else
{
lean_dec(v_t_148_);
return v_k_149_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim(lean_object* v_motive_152_, lean_object* v_ctorIdx_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_k_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_154_, v_k_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_ctorElim___boxed(lean_object* v_motive_158_, lean_object* v_ctorIdx_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_k_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = lp_Multi_T_Dom_ctorElim(v_motive_158_, v_ctorIdx_159_, v_t_160_, v_h_161_, v_k_162_);
lean_dec(v_ctorIdx_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_Zero_elim___redArg(lean_object* v_t_164_, lean_object* v_Zero_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_164_, v_Zero_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_Zero_elim(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_Zero_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_168_, v_Zero_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_One_elim___redArg(lean_object* v_t_172_, lean_object* v_One_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_172_, v_One_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_One_elim(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_One_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_176_, v_One_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03c9_elim___redArg(lean_object* v_t_180_, lean_object* v_00_u03c9_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_180_, v_00_u03c9_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03c9_elim(lean_object* v_motive_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_00_u03c9_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_184_, v_00_u03c9_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03a9_elim___redArg(lean_object* v_t_188_, lean_object* v_00_u03a9_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_188_, v_00_u03a9_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Dom_00_u03a9_elim(lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_00_u03a9_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lp_Multi_T_Dom_ctorElim___redArg(v_t_192_, v_00_u03a9_194_);
return v___x_195_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_instDecidableEqDom_decEq(lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
switch(lean_obj_tag(v_x_196_))
{
case 0:
{
switch(lean_obj_tag(v_x_197_))
{
case 0:
{
uint8_t v___x_198_; 
v___x_198_ = 1;
return v___x_198_;
}
case 3:
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
default: 
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_197_))
{
case 1:
{
uint8_t v___x_201_; 
v___x_201_ = 1;
return v___x_201_;
}
case 3:
{
uint8_t v___x_202_; 
v___x_202_ = 0;
return v___x_202_;
}
default: 
{
uint8_t v___x_203_; 
v___x_203_ = 0;
return v___x_203_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_x_197_))
{
case 2:
{
uint8_t v___x_204_; 
v___x_204_ = 1;
return v___x_204_;
}
case 3:
{
uint8_t v___x_205_; 
v___x_205_ = 0;
return v___x_205_;
}
default: 
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
}
}
default: 
{
lean_object* v_l0_207_; uint8_t v___x_208_; 
v_l0_207_ = lean_ctor_get(v_x_196_, 0);
v___x_208_ = 0;
if (lean_obj_tag(v_x_197_) == 3)
{
lean_object* v_l0_209_; uint8_t v___x_210_; 
v_l0_209_ = lean_ctor_get(v_x_197_, 0);
v___x_210_ = lp_Multi_instDecidableEqT_decEq(v_l0_207_, v_l0_209_);
if (v___x_210_ == 0)
{
return v___x_208_;
}
else
{
return v___x_210_;
}
}
else
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_instDecidableEqDom_decEq___boxed(lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = lp_Multi_T_instDecidableEqDom_decEq(v_x_211_, v_x_212_);
lean_dec(v_x_212_);
lean_dec(v_x_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_instDecidableEqDom(lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
uint8_t v___x_217_; 
v___x_217_ = lp_Multi_T_instDecidableEqDom_decEq(v_x_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_instDecidableEqDom___boxed(lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = lp_Multi_T_instDecidableEqDom(v_x_218_, v_x_219_);
lean_dec(v_x_219_);
lean_dec(v_x_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_dom(lean_object* v_s_222_){
_start:
{
if (lean_obj_tag(v_s_222_) == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
else
{
lean_object* v_s0_224_; lean_object* v_s1_225_; lean_object* v_s2_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_s0_224_ = lean_ctor_get(v_s_222_, 0);
v_s1_225_ = lean_ctor_get(v_s_222_, 1);
v_s2_226_ = lean_ctor_get(v_s_222_, 2);
v___x_227_ = lean_box(0);
v___x_228_ = lp_Multi_instDecidableEqT_decEq(v_s2_226_, v___x_227_);
if (v___x_228_ == 0)
{
v_s_222_ = v_s2_226_;
goto _start;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lp_Multi_T_dom(v_s1_225_);
switch(lean_obj_tag(v___x_230_))
{
case 0:
{
lean_object* v___x_231_; 
v___x_231_ = lp_Multi_T_dom(v_s0_224_);
switch(lean_obj_tag(v___x_231_))
{
case 0:
{
lean_object* v___x_232_; 
v___x_232_ = lean_box(1);
return v___x_232_;
}
case 1:
{
lean_object* v___x_233_; 
lean_inc(v_s0_224_);
v___x_233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_233_, 0, v_s0_224_);
return v___x_233_;
}
default: 
{
return v___x_231_;
}
}
}
case 1:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(2);
return v___x_234_;
}
case 2:
{
return v___x_230_;
}
default: 
{
lean_object* v_l0_235_; uint8_t v___x_236_; 
v_l0_235_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_l0_235_);
v___x_236_ = lp_Multi_T_decLt(v_s0_224_, v_l0_235_);
lean_dec(v_l0_235_);
if (v___x_236_ == 0)
{
return v___x_230_;
}
else
{
lean_object* v___x_237_; 
lean_dec_ref_known(v___x_230_, 1);
v___x_237_ = lean_box(2);
return v___x_237_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_dom___boxed(lean_object* v_s_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = lp_Multi_T_dom(v_s_238_);
lean_dec(v_s_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_iter_match__1_splitter___redArg(lean_object* v_x_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v_h__2_242_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_apply_1(v_h__1_241_, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v_s0_245_; lean_object* v_s1_246_; lean_object* v_s2_247_; lean_object* v___x_248_; 
lean_dec(v_h__1_241_);
v_s0_245_ = lean_ctor_get(v_x_240_, 0);
lean_inc(v_s0_245_);
v_s1_246_ = lean_ctor_get(v_x_240_, 1);
lean_inc(v_s1_246_);
v_s2_247_ = lean_ctor_get(v_x_240_, 2);
lean_inc(v_s2_247_);
lean_dec_ref_known(v_x_240_, 3);
v___x_248_ = lean_apply_3(v_h__2_242_, v_s0_245_, v_s1_246_, v_s2_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_iter_match__1_splitter(lean_object* v_motive_249_, lean_object* v_x_250_, lean_object* v_h__1_251_, lean_object* v_h__2_252_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_h__2_252_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_apply_1(v_h__1_251_, v___x_253_);
return v___x_254_;
}
else
{
lean_object* v_s0_255_; lean_object* v_s1_256_; lean_object* v_s2_257_; lean_object* v___x_258_; 
lean_dec(v_h__1_251_);
v_s0_255_ = lean_ctor_get(v_x_250_, 0);
lean_inc(v_s0_255_);
v_s1_256_ = lean_ctor_get(v_x_250_, 1);
lean_inc(v_s1_256_);
v_s2_257_ = lean_ctor_get(v_x_250_, 2);
lean_inc(v_s2_257_);
lean_dec_ref_known(v_x_250_, 3);
v___x_258_ = lean_apply_3(v_h__2_252_, v_s0_255_, v_s1_256_, v_s2_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_dom_match__1_splitter___redArg(lean_object* v_x_259_, lean_object* v_h__1_260_, lean_object* v_h__2_261_, lean_object* v_h__3_262_, lean_object* v_h__4_263_){
_start:
{
switch(lean_obj_tag(v_x_259_))
{
case 0:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_h__4_263_);
lean_dec(v_h__3_262_);
lean_dec(v_h__2_261_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_apply_1(v_h__1_260_, v___x_264_);
return v___x_265_;
}
case 1:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec(v_h__4_263_);
lean_dec(v_h__3_262_);
lean_dec(v_h__1_260_);
v___x_266_ = lean_box(0);
v___x_267_ = lean_apply_1(v_h__2_261_, v___x_266_);
return v___x_267_;
}
case 2:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_h__4_263_);
lean_dec(v_h__2_261_);
lean_dec(v_h__1_260_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_1(v_h__3_262_, v___x_268_);
return v___x_269_;
}
default: 
{
lean_object* v_l0_270_; lean_object* v___x_271_; 
lean_dec(v_h__3_262_);
lean_dec(v_h__2_261_);
lean_dec(v_h__1_260_);
v_l0_270_ = lean_ctor_get(v_x_259_, 0);
lean_inc(v_l0_270_);
lean_dec_ref_known(v_x_259_, 1);
v___x_271_ = lean_apply_1(v_h__4_263_, v_l0_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_dom_match__1_splitter(lean_object* v_motive_272_, lean_object* v_x_273_, lean_object* v_h__1_274_, lean_object* v_h__2_275_, lean_object* v_h__3_276_, lean_object* v_h__4_277_){
_start:
{
switch(lean_obj_tag(v_x_273_))
{
case 0:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_h__4_277_);
lean_dec(v_h__3_276_);
lean_dec(v_h__2_275_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_apply_1(v_h__1_274_, v___x_278_);
return v___x_279_;
}
case 1:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_h__4_277_);
lean_dec(v_h__3_276_);
lean_dec(v_h__1_274_);
v___x_280_ = lean_box(0);
v___x_281_ = lean_apply_1(v_h__2_275_, v___x_280_);
return v___x_281_;
}
case 2:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v_h__4_277_);
lean_dec(v_h__2_275_);
lean_dec(v_h__1_274_);
v___x_282_ = lean_box(0);
v___x_283_ = lean_apply_1(v_h__3_276_, v___x_282_);
return v___x_283_;
}
default: 
{
lean_object* v_l0_284_; lean_object* v___x_285_; 
lean_dec(v_h__3_276_);
lean_dec(v_h__2_275_);
lean_dec(v_h__1_274_);
v_l0_284_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_l0_284_);
lean_dec_ref_known(v_x_273_, 1);
v___x_285_ = lean_apply_1(v_h__4_277_, v_l0_284_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0___boxed(lean_object* v_s1_286_, lean_object* v_l_x27_287_, lean_object* v___x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = lp_Multi_T_fund___lam__0(v_s1_286_, v_l_x27_287_, v___x_288_, v_x_289_);
lean_dec(v_x_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund(lean_object* v_s_291_, lean_object* v_t_292_){
_start:
{
if (lean_obj_tag(v_s_291_) == 0)
{
return v_s_291_;
}
else
{
lean_object* v_s0_293_; lean_object* v_s1_294_; lean_object* v_s2_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_333_; 
v_s0_293_ = lean_ctor_get(v_s_291_, 0);
v_s1_294_ = lean_ctor_get(v_s_291_, 1);
v_s2_295_ = lean_ctor_get(v_s_291_, 2);
v_isSharedCheck_333_ = !lean_is_exclusive(v_s_291_);
if (v_isSharedCheck_333_ == 0)
{
v___x_297_ = v_s_291_;
v_isShared_298_ = v_isSharedCheck_333_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_s2_295_);
lean_inc(v_s1_294_);
lean_inc(v_s0_293_);
lean_dec(v_s_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_333_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = lp_Multi_instDecidableEqT_decEq(v_s2_295_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lp_Multi_T_fund(v_s2_295_, v_t_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_301_);
v___x_303_ = v___x_297_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_s0_293_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_s1_294_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v___x_301_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
else
{
lean_object* v___x_305_; 
lean_dec(v_s2_295_);
v___x_305_ = lp_Multi_T_dom(v_s1_294_);
switch(lean_obj_tag(v___x_305_))
{
case 0:
{
lean_object* v___x_306_; 
lean_dec(v_s1_294_);
v___x_306_ = lp_Multi_T_dom(v_s0_293_);
switch(lean_obj_tag(v___x_306_))
{
case 0:
{
lean_del_object(v___x_297_);
lean_dec(v_s0_293_);
return v___x_299_;
}
case 1:
{
lean_del_object(v___x_297_);
lean_dec(v_s0_293_);
lean_inc(v_t_292_);
return v_t_292_;
}
default: 
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v___x_306_);
v___x_307_ = lp_Multi_T_fund(v_s0_293_, v_t_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_299_);
lean_ctor_set(v___x_297_, 1, v___x_299_);
lean_ctor_set(v___x_297_, 0, v___x_307_);
v___x_309_ = v___x_297_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_299_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
case 1:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lp_Multi_T_fund(v_s1_294_, v___x_299_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_299_);
lean_ctor_set(v___x_297_, 1, v___x_311_);
v___x_313_ = v___x_297_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_s0_293_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v___x_299_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lp_Multi_T_mul(v___x_313_, v_t_292_);
lean_dec_ref(v___x_313_);
return v___x_314_;
}
}
case 2:
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = lp_Multi_T_fund(v_s1_294_, v_t_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_299_);
lean_ctor_set(v___x_297_, 1, v___x_316_);
v___x_318_ = v___x_297_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_s0_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v___x_299_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
default: 
{
lean_object* v_l0_320_; uint8_t v___x_321_; 
v_l0_320_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_l0_320_);
lean_dec_ref_known(v___x_305_, 1);
v___x_321_ = lp_Multi_T_decLt(v_s0_293_, v_l0_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec(v_l0_320_);
v___x_322_ = lp_Multi_T_fund(v_s1_294_, v_t_292_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_299_);
lean_ctor_set(v___x_297_, 1, v___x_322_);
v___x_324_ = v___x_297_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_s0_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___x_299_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
else
{
lean_object* v_l_x27_326_; lean_object* v_F_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v_l_x27_326_ = lp_Multi_T_fund(v_l0_320_, v___x_299_);
lean_inc(v_s1_294_);
v_F_327_ = lean_alloc_closure((void*)(lp_Multi_T_fund___lam__0___boxed), 4, 3);
lean_closure_set(v_F_327_, 0, v_s1_294_);
lean_closure_set(v_F_327_, 1, v_l_x27_326_);
lean_closure_set(v_F_327_, 2, v___x_299_);
v___x_328_ = lp_Multi_T_iter(v_F_327_, v_t_292_);
v___x_329_ = lp_Multi_T_fund(v_s1_294_, v___x_328_);
lean_dec(v___x_328_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 2, v___x_299_);
lean_ctor_set(v___x_297_, 1, v___x_329_);
v___x_331_ = v___x_297_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_s0_293_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v___x_299_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___lam__0(lean_object* v_s1_334_, lean_object* v_l_x27_335_, lean_object* v___x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lp_Multi_T_fund(v_s1_334_, v_x_337_);
v___x_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_339_, 0, v_l_x27_335_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_ctor_set(v___x_339_, 2, v___x_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_fund___boxed(lean_object* v_s_340_, lean_object* v_t_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = lp_Multi_T_fund(v_s_340_, v_t_341_);
lean_dec(v_t_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_fund_match__1_splitter___redArg(lean_object* v_x_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_, lean_object* v_h__3_346_, lean_object* v_h__4_347_){
_start:
{
switch(lean_obj_tag(v_x_343_))
{
case 0:
{
lean_object* v___x_348_; 
lean_dec(v_h__4_347_);
lean_dec(v_h__3_346_);
lean_dec(v_h__2_345_);
v___x_348_ = lean_apply_1(v_h__1_344_, lean_box(0));
return v___x_348_;
}
case 1:
{
lean_object* v___x_349_; 
lean_dec(v_h__4_347_);
lean_dec(v_h__3_346_);
lean_dec(v_h__1_344_);
v___x_349_ = lean_apply_1(v_h__2_345_, lean_box(0));
return v___x_349_;
}
case 2:
{
lean_object* v___x_350_; 
lean_dec(v_h__4_347_);
lean_dec(v_h__2_345_);
lean_dec(v_h__1_344_);
v___x_350_ = lean_apply_1(v_h__3_346_, lean_box(0));
return v___x_350_;
}
default: 
{
lean_object* v_l0_351_; lean_object* v___x_352_; 
lean_dec(v_h__3_346_);
lean_dec(v_h__2_345_);
lean_dec(v_h__1_344_);
v_l0_351_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_l0_351_);
lean_dec_ref_known(v_x_343_, 1);
v___x_352_ = lean_apply_2(v_h__4_347_, v_l0_351_, lean_box(0));
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_fund_match__1_splitter(lean_object* v_motive_353_, lean_object* v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_, lean_object* v_h__3_357_, lean_object* v_h__4_358_){
_start:
{
switch(lean_obj_tag(v_x_354_))
{
case 0:
{
lean_object* v___x_359_; 
lean_dec(v_h__4_358_);
lean_dec(v_h__3_357_);
lean_dec(v_h__2_356_);
v___x_359_ = lean_apply_1(v_h__1_355_, lean_box(0));
return v___x_359_;
}
case 1:
{
lean_object* v___x_360_; 
lean_dec(v_h__4_358_);
lean_dec(v_h__3_357_);
lean_dec(v_h__1_355_);
v___x_360_ = lean_apply_1(v_h__2_356_, lean_box(0));
return v___x_360_;
}
case 2:
{
lean_object* v___x_361_; 
lean_dec(v_h__4_358_);
lean_dec(v_h__2_356_);
lean_dec(v_h__1_355_);
v___x_361_ = lean_apply_1(v_h__3_357_, lean_box(0));
return v___x_361_;
}
default: 
{
lean_object* v_l0_362_; lean_object* v___x_363_; 
lean_dec(v_h__3_357_);
lean_dec(v_h__2_356_);
lean_dec(v_h__1_355_);
v_l0_362_ = lean_ctor_get(v_x_354_, 0);
lean_inc(v_l0_362_);
lean_dec_ref_known(v_x_354_, 1);
v___x_363_ = lean_apply_2(v_h__4_358_, v_l0_362_, lean_box(0));
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_head(lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
return v_x_364_;
}
else
{
lean_object* v_s0_365_; lean_object* v_s1_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_s0_365_ = lean_ctor_get(v_x_364_, 0);
v_s1_366_ = lean_ctor_get(v_x_364_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_x_364_, 2);
lean_dec(v_unused_375_);
v___x_368_ = v_x_364_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_s1_366_);
lean_inc(v_s0_365_);
lean_dec(v_x_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 2, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_s0_365_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_s1_366_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_G(lean_object* v_u_376_, lean_object* v_s_377_){
_start:
{
if (lean_obj_tag(v_s_377_) == 0)
{
lean_object* v___x_378_; 
lean_dec(v_u_376_);
v___x_378_ = lean_box(0);
return v___x_378_;
}
else
{
lean_object* v_s0_379_; lean_object* v_s1_380_; lean_object* v_s2_381_; lean_object* v_Gs0_382_; lean_object* v_Gs2_383_; lean_object* v___x_384_; uint8_t v___x_385_; uint8_t v___x_386_; 
v_s0_379_ = lean_ctor_get(v_s_377_, 0);
lean_inc_n(v_s0_379_, 2);
v_s1_380_ = lean_ctor_get(v_s_377_, 1);
lean_inc(v_s1_380_);
v_s2_381_ = lean_ctor_get(v_s_377_, 2);
lean_inc(v_s2_381_);
lean_dec_ref_known(v_s_377_, 3);
lean_inc_n(v_u_376_, 3);
v_Gs0_382_ = lp_Multi_T_G(v_u_376_, v_s0_379_);
v_Gs2_383_ = lp_Multi_T_G(v_u_376_, v_s2_381_);
v___x_384_ = lean_alloc_closure((void*)(lp_Multi_instDecidableEqT___boxed), 2, 0);
v___x_385_ = lp_Multi_T_decLt(v_u_376_, v_s0_379_);
v___x_386_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v_u_376_, v_s0_379_, v___x_384_, v___x_385_);
if (v___x_386_ == 0)
{
lean_dec(v_Gs0_382_);
lean_dec(v_s1_380_);
lean_dec(v_u_376_);
return v_Gs2_383_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = lean_box(0);
lean_inc(v_s1_380_);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v_s1_380_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_List_appendTR___redArg(v___x_388_, v_Gs0_382_);
v___x_390_ = lp_Multi_T_G(v_u_376_, v_s1_380_);
v___x_391_ = l_List_appendTR___redArg(v___x_389_, v___x_390_);
v___x_392_ = l_List_appendTR___redArg(v___x_391_, v_Gs2_383_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_LF(lean_object* v_n_393_){
_start:
{
lean_object* v_zero_394_; uint8_t v_isZero_395_; 
v_zero_394_ = lean_unsigned_to_nat(0u);
v_isZero_395_ = lean_nat_dec_eq(v_n_393_, v_zero_394_);
if (v_isZero_395_ == 1)
{
lean_object* v___x_396_; 
v___x_396_ = lean_box(0);
return v___x_396_;
}
else
{
lean_object* v_one_397_; lean_object* v_n_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_one_397_ = lean_unsigned_to_nat(1u);
v_n_398_ = lean_nat_sub(v_n_393_, v_one_397_);
v___x_399_ = lp_Multi_T_LF(v_n_398_);
lean_dec(v_n_398_);
v___x_400_ = lean_box(0);
v___x_401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_LF___boxed(lean_object* v_n_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = lp_Multi_T_LF(v_n_402_);
lean_dec(v_n_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ofNat(lean_object* v_x_404_){
_start:
{
lean_object* v_zero_405_; uint8_t v_isZero_406_; 
v_zero_405_ = lean_unsigned_to_nat(0u);
v_isZero_406_ = lean_nat_dec_eq(v_x_404_, v_zero_405_);
if (v_isZero_406_ == 1)
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
return v___x_407_;
}
else
{
lean_object* v_one_408_; lean_object* v_n_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_one_408_ = lean_unsigned_to_nat(1u);
v_n_409_ = lean_nat_sub(v_x_404_, v_one_408_);
v___x_410_ = lean_box(0);
v___x_411_ = lp_Multi_T_ofNat(v_n_409_);
lean_dec(v_n_409_);
v___x_412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_411_);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_ofNat___boxed(lean_object* v_x_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = lp_Multi_T_ofNat(v_x_413_);
lean_dec(v_x_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_mul_match__1_splitter___redArg(lean_object* v_x_415_, lean_object* v_x_416_, lean_object* v_h__1_417_, lean_object* v_h__2_418_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v___x_419_; 
lean_dec(v_h__2_418_);
v___x_419_ = lean_apply_1(v_h__1_417_, v_x_415_);
return v___x_419_;
}
else
{
lean_object* v_s0_420_; lean_object* v_s1_421_; lean_object* v_s2_422_; lean_object* v___x_423_; 
lean_dec(v_h__1_417_);
v_s0_420_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_s0_420_);
v_s1_421_ = lean_ctor_get(v_x_416_, 1);
lean_inc(v_s1_421_);
v_s2_422_ = lean_ctor_get(v_x_416_, 2);
lean_inc(v_s2_422_);
lean_dec_ref_known(v_x_416_, 3);
v___x_423_ = lean_apply_4(v_h__2_418_, v_x_415_, v_s0_420_, v_s1_421_, v_s2_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_Term2Syntax_0__T_mul_match__1_splitter(lean_object* v_motive_424_, lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v___x_429_; 
lean_dec(v_h__2_428_);
v___x_429_ = lean_apply_1(v_h__1_427_, v_x_425_);
return v___x_429_;
}
else
{
lean_object* v_s0_430_; lean_object* v_s1_431_; lean_object* v_s2_432_; lean_object* v___x_433_; 
lean_dec(v_h__1_427_);
v_s0_430_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_s0_430_);
v_s1_431_ = lean_ctor_get(v_x_426_, 1);
lean_inc(v_s1_431_);
v_s2_432_ = lean_ctor_get(v_x_426_, 2);
lean_inc(v_s2_432_);
lean_dec_ref_known(v_x_426_, 3);
v___x_433_ = lean_apply_4(v_h__2_428_, v_x_425_, v_s0_430_, v_s1_431_, v_s2_432_);
return v___x_433_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_order(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_Term2Syntax(uint8_t builtin) {
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
