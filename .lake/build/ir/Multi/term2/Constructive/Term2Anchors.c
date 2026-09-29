// Lean compiler output
// Module: Multi.term2.Constructive.Term2Anchors
// Imports: public import Init public meta import Init public import Multi.term2.Constructive.Term2Stages
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
lean_object* lp_Multi_T_ofNat(lean_object*);
lean_object* lp_Multi_T_dom(lean_object*);
lean_object* lp_Multi_T_fund(lean_object*, lean_object*);
static lean_once_cell_t lp_Multi_T_Constructive_anchor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Constructive_anchor___closed__0;
LEAN_EXPORT lean_object* lp_Multi_T_Constructive_anchor(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Constructive_anchor___boxed(lean_object*);
static lean_object* _init_lp_Multi_T_Constructive_anchor___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lp_Multi_T_ofNat(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Constructive_anchor(lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lp_Multi_T_dom(v_s_3_);
switch(lean_obj_tag(v___x_4_))
{
case 3:
{
lean_object* v_l0_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_l0_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_l0_5_);
lean_dec_ref_known(v___x_4_, 1);
v___x_6_ = lean_box(0);
v___x_7_ = lp_Multi_T_fund(v_l0_5_, v___x_6_);
v___x_8_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_6_);
return v___x_8_;
}
case 2:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&lp_Multi_T_Constructive_anchor___closed__0, &lp_Multi_T_Constructive_anchor___closed__0_once, _init_lp_Multi_T_Constructive_anchor___closed__0);
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
lean_dec(v___x_4_);
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Constructive_anchor___boxed(lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_Multi_T_Constructive_anchor(v_s_11_);
lean_dec(v_s_11_);
return v_res_12_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term2_Constructive_Term2Stages(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term2_Constructive_Term2Anchors(uint8_t builtin) {
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
res = initialize_Multi_Multi_term2_Constructive_Term2Stages(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
