// Lean compiler output
// Module: Multi.term2.OCF.Collapse
// Imports: public import Init public meta import Init public import Multi.term2.OCF.Hartogs public import Multi.term2.OCF.Arithmetic
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
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx___redArg(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lp_Multi_OCF_ClosureCode_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx(lean_object* v_X_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_Multi_OCF_ClosureCode_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorIdx___boxed(lean_object* v_X_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lp_Multi_OCF_ClosureCode_ctorIdx(v_X_9_, v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
if (lean_obj_tag(v_t_12_) == 0)
{
lean_object* v_x_14_; lean_object* v___x_15_; 
v_x_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_x_14_);
lean_dec_ref_known(v_t_12_, 1);
v___x_15_ = lean_apply_1(v_k_13_, v_x_14_);
return v___x_15_;
}
else
{
lean_object* v_index_16_; lean_object* v_argument_17_; lean_object* v_tail_18_; lean_object* v___x_19_; 
v_index_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_index_16_);
v_argument_17_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_argument_17_);
v_tail_18_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_tail_18_);
lean_dec_ref_known(v_t_12_, 3);
v___x_19_ = lean_apply_3(v_k_13_, v_index_16_, v_argument_17_, v_tail_18_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorElim(lean_object* v_X_20_, lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_Multi_OCF_ClosureCode_ctorElim___redArg(v_t_23_, v_k_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_ctorElim___boxed(lean_object* v_X_27_, lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lp_Multi_OCF_ClosureCode_ctorElim(v_X_27_, v_motive_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_leaf_elim___redArg(lean_object* v_t_34_, lean_object* v_leaf_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_Multi_OCF_ClosureCode_ctorElim___redArg(v_t_34_, v_leaf_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_leaf_elim(lean_object* v_X_37_, lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_leaf_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_Multi_OCF_ClosureCode_ctorElim___redArg(v_t_39_, v_leaf_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_node_elim___redArg(lean_object* v_t_43_, lean_object* v_node_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_Multi_OCF_ClosureCode_ctorElim___redArg(v_t_43_, v_node_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_Multi_OCF_ClosureCode_node_elim(lean_object* v_X_46_, lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_node_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lp_Multi_OCF_ClosureCode_ctorElim___redArg(v_t_48_, v_node_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter___redArg(lean_object* v_c_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
if (lean_obj_tag(v_c_52_) == 0)
{
lean_object* v_x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_54_);
v_x_55_ = lean_ctor_get(v_c_52_, 0);
lean_inc(v_x_55_);
lean_dec_ref_known(v_c_52_, 1);
v___x_56_ = lean_apply_1(v_h__1_53_, v_x_55_);
return v___x_56_;
}
else
{
lean_object* v_index_57_; lean_object* v_argument_58_; lean_object* v_tail_59_; lean_object* v___x_60_; 
lean_dec(v_h__1_53_);
v_index_57_ = lean_ctor_get(v_c_52_, 0);
lean_inc_ref(v_index_57_);
v_argument_58_ = lean_ctor_get(v_c_52_, 1);
lean_inc_ref(v_argument_58_);
v_tail_59_ = lean_ctor_get(v_c_52_, 2);
lean_inc_ref(v_tail_59_);
lean_dec_ref_known(v_c_52_, 3);
v___x_60_ = lean_apply_3(v_h__2_54_, v_index_57_, v_argument_58_, v_tail_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter(lean_object* v_00_u03a9_61_, lean_object* v_v_62_, lean_object* v_motive_63_, lean_object* v_c_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
if (lean_obj_tag(v_c_64_) == 0)
{
lean_object* v_x_67_; lean_object* v___x_68_; 
lean_dec(v_h__2_66_);
v_x_67_ = lean_ctor_get(v_c_64_, 0);
lean_inc(v_x_67_);
lean_dec_ref_known(v_c_64_, 1);
v___x_68_ = lean_apply_1(v_h__1_65_, v_x_67_);
return v___x_68_;
}
else
{
lean_object* v_index_69_; lean_object* v_argument_70_; lean_object* v_tail_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_65_);
v_index_69_ = lean_ctor_get(v_c_64_, 0);
lean_inc_ref(v_index_69_);
v_argument_70_ = lean_ctor_get(v_c_64_, 1);
lean_inc_ref(v_argument_70_);
v_tail_71_ = lean_ctor_get(v_c_64_, 2);
lean_inc_ref(v_tail_71_);
lean_dec_ref_known(v_c_64_, 3);
v___x_72_ = lean_apply_3(v_h__2_66_, v_index_69_, v_argument_70_, v_tail_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter___boxed(lean_object* v_00_u03a9_73_, lean_object* v_v_74_, lean_object* v_motive_75_, lean_object* v_c_76_, lean_object* v_h__1_77_, lean_object* v_h__2_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = lp_Multi___private_Multi_term2_OCF_Collapse_0__OCF_Collapse_evaluate_match__1_splitter(v_00_u03a9_73_, v_v_74_, v_motive_75_, v_c_76_, v_h__1_77_, v_h__2_78_);
lean_dec(v_v_74_);
lean_dec(v_00_u03a9_73_);
return v_res_79_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term2_OCF_Hartogs(uint8_t builtin);
lean_object* initialize_Multi_Multi_term2_OCF_Arithmetic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term2_OCF_Collapse(uint8_t builtin) {
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
res = initialize_Multi_Multi_term2_OCF_Hartogs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Multi_Multi_term2_OCF_Arithmetic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
