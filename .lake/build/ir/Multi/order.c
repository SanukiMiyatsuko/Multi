// Lean compiler output
// Module: Multi.order
// Imports: public import Init public meta import Init
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
LEAN_EXPORT lean_object* lp_Multi_instLE__multi(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_instDecidableLeOfDecidableEqOfLt__multi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_instLE__multi__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_instLE__multi(lean_object* v_A_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(lean_object* v_a_4_, lean_object* v_b_5_, lean_object* v_inst_6_, uint8_t v_inst_7_){
_start:
{
if (v_inst_7_ == 0)
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_apply_2(v_inst_6_, v_a_4_, v_b_5_);
v___x_9_ = lean_unbox(v___x_8_);
return v___x_9_;
}
else
{
lean_dec_ref(v_inst_6_);
lean_dec(v_b_5_);
lean_dec(v_a_4_);
return v_inst_7_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg___boxed(lean_object* v_a_10_, lean_object* v_b_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
uint8_t v_inst_39__boxed_14_; uint8_t v_res_15_; lean_object* v_r_16_; 
v_inst_39__boxed_14_ = lean_unbox(v_inst_13_);
v_res_15_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v_a_10_, v_b_11_, v_inst_12_, v_inst_39__boxed_14_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t lp_Multi_instDecidableLeOfDecidableEqOfLt__multi(lean_object* v_A_17_, lean_object* v_inst_18_, lean_object* v_a_19_, lean_object* v_b_20_, lean_object* v_inst_21_, uint8_t v_inst_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___redArg(v_a_19_, v_b_20_, v_inst_21_, v_inst_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_Multi_instDecidableLeOfDecidableEqOfLt__multi___boxed(lean_object* v_A_24_, lean_object* v_inst_25_, lean_object* v_a_26_, lean_object* v_b_27_, lean_object* v_inst_28_, lean_object* v_inst_29_){
_start:
{
uint8_t v_inst_50__boxed_30_; uint8_t v_res_31_; lean_object* v_r_32_; 
v_inst_50__boxed_30_ = lean_unbox(v_inst_29_);
v_res_31_ = lp_Multi_instDecidableLeOfDecidableEqOfLt__multi(v_A_24_, v_inst_25_, v_a_26_, v_b_27_, v_inst_28_, v_inst_50__boxed_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* lp_Multi_instLE__multi__1(lean_object* v_A_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_order(uint8_t builtin) {
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
