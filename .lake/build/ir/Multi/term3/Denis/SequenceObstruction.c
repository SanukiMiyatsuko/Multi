// Lean compiler output
// Module: Multi.term3.Denis.SequenceObstruction
// Imports: public import Init public meta import Init public import Multi.term3.Term3DenisOrder
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
extern lean_object* lp_Multi_T_Correspondence_Denis_cardFixed;
static lean_once_cell_t lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__0;
static lean_once_cell_t lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__1;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_obstructionIndexTerm;
static lean_once_cell_t lp_Multi_T_Correspondence_Denis_obstructionTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_Denis_obstructionTerm___closed__0;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_obstructionTerm;
static lean_object* _init_lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lp_Multi_T_Correspondence_Denis_one;
v___x_2_ = lp_Multi_T_Correspondence_Denis_cardFixed;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__0, &lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__0_once, _init_lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__0);
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_Denis_obstructionIndexTerm(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__1, &lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__1_once, _init_lp_Multi_T_Correspondence_Denis_obstructionIndexTerm___closed__1);
return v___x_7_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_Denis_obstructionTerm___closed__0(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = lp_Multi_T_Correspondence_Denis_obstructionIndexTerm;
v___x_10_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_Denis_obstructionTerm(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_obstructionTerm___closed__0, &lp_Multi_T_Correspondence_Denis_obstructionTerm___closed__0_once, _init_lp_Multi_T_Correspondence_Denis_obstructionTerm___closed__0);
return v___x_11_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Term3DenisOrder(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Denis_SequenceObstruction(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Term3DenisOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Multi_T_Correspondence_Denis_obstructionIndexTerm = _init_lp_Multi_T_Correspondence_Denis_obstructionIndexTerm();
lean_mark_persistent(lp_Multi_T_Correspondence_Denis_obstructionIndexTerm);
lp_Multi_T_Correspondence_Denis_obstructionTerm = _init_lp_Multi_T_Correspondence_Denis_obstructionTerm();
lean_mark_persistent(lp_Multi_T_Correspondence_Denis_obstructionTerm);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
