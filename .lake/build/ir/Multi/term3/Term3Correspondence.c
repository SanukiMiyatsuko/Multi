// Lean compiler output
// Module: Multi.term3.Term3Correspondence
// Imports: public import Init public meta import Init public import Multi.term3.Term3Normal
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lp_Multi_instDecidableEqT_decEq(lean_object*, lean_object*);
static const lean_ctor_object lp_Multi_T_Correspondence_one___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_one___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_one___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_one = (const lean_object*)&lp_Multi_T_Correspondence_one___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_exp(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_card(lean_object*);
static lean_once_cell_t lp_Multi_T_Correspondence_uncountable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_uncountable___closed__0;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_uncountable;
static const lean_ctor_object lp_Multi_T_Correspondence_inaccessible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 1}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_one___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_inaccessible___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_inaccessible___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_inaccessible = (const lean_object*)&lp_Multi_T_Correspondence_inaccessible___closed__0_value;
static lean_once_cell_t lp_Multi_T_Correspondence_epsilon___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_epsilon___closed__0;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_epsilon;
static lean_once_cell_t lp_Multi_T_Correspondence_collapseI___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_collapseI___closed__0;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_collapseI;
static lean_once_cell_t lp_Multi_T_Correspondence_cardFixed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_cardFixed___closed__0;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_cardFixed;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_iterate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_iterate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_zero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_zero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_I_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_I_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_psi_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_psi_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_Multi_T_Correspondence_Denis_instDecidableEqTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instDecidableEqTerm___boxed(lean_object*, lean_object*);
static const lean_string_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "T.Correspondence.Denis.Term.zero"};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__0_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__0_value)}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__1 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__1_value;
static lean_once_cell_t lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2;
static lean_once_cell_t lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3;
static const lean_string_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "T.Correspondence.Denis.Term.add"};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__4 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__4_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__4_value)}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__5 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__5_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__6 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__6_value;
static const lean_string_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "T.Correspondence.Denis.Term.I"};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__7 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__7_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__7_value)}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__8 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__8_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__9 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__9_value;
static const lean_string_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "T.Correspondence.Denis.Term.psi"};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__10 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__10_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__10_value)}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__11 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__11_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__12 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__12_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Multi_T_Correspondence_Denis_instReprTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Multi_T_Correspondence_Denis_instReprTerm_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm = (const lean_object*)&lp_Multi_T_Correspondence_Denis_instReprTerm___closed__0_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_omega1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_omega1___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_omega1___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_omega1 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_omega1___closed__0_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_I1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_omega1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_I1___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__0_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_I1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_I1___closed__1 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__1_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_I1 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__1_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_one = (const lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_exp(lean_object*);
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_epsilon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_omega1___closed__0_value),((lean_object*)&lp_Multi_T_Correspondence_Denis_omega1___closed__0_value)}};
static const lean_object* lp_Multi_T_Correspondence_Denis_epsilon___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_epsilon___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_epsilon = (const lean_object*)&lp_Multi_T_Correspondence_Denis_epsilon___closed__0_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_collapseI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_omega1___closed__0_value),((lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__1_value)}};
static const lean_object* lp_Multi_T_Correspondence_Denis_collapseI___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_collapseI___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_collapseI = (const lean_object*)&lp_Multi_T_Correspondence_Denis_collapseI___closed__0_value;
static const lean_ctor_object lp_Multi_T_Correspondence_Denis_cardFixed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 3}, .m_objs = {((lean_object*)&lp_Multi_T_Correspondence_Denis_I1___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_Denis_cardFixed___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_cardFixed___closed__0_value;
LEAN_EXPORT const lean_object* lp_Multi_T_Correspondence_Denis_cardFixed = (const lean_object*)&lp_Multi_T_Correspondence_Denis_cardFixed___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_iterate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_iterate___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_Multi_T_Correspondence_Denis_epsilonSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Multi_T_Correspondence_Denis_exp, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Multi_T_Correspondence_Denis_epsilonSeq___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_epsilonSeq___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_epsilonSeq(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_epsilonSeq___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq___lam__0(lean_object*);
static const lean_closure_object lp_Multi_T_Correspondence_Denis_cardFixedSeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Multi_T_Correspondence_Denis_cardFixedSeq___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_cardFixedSeq___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq___lam__0(lean_object*);
static const lean_closure_object lp_Multi_T_Correspondence_Denis_collapseISeq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Multi_T_Correspondence_Denis_collapseISeq___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_Denis_collapseISeq___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq___boxed(lean_object*);
static const lean_ctor_object lp_Multi_T_Correspondence_direct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_Multi_T_Correspondence_direct___closed__0 = (const lean_object*)&lp_Multi_T_Correspondence_direct___closed__0_value;
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_direct(lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_direct___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_direct_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_direct_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_exp(lean_object* v_a_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v_a_4_);
lean_ctor_set(v___x_6_, 3, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_card(lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
lean_ctor_set(v___x_9_, 1, v_a_7_);
lean_ctor_set(v___x_9_, 2, v___x_8_);
lean_ctor_set(v___x_9_, 3, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_uncountable___closed__0(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(lp_Multi_T_Correspondence_one));
v___x_11_ = lp_Multi_T_Correspondence_card(v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_uncountable(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&lp_Multi_T_Correspondence_uncountable___closed__0, &lp_Multi_T_Correspondence_uncountable___closed__0_once, _init_lp_Multi_T_Correspondence_uncountable___closed__0);
return v___x_12_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_epsilon___closed__0(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lp_Multi_T_Correspondence_uncountable;
v___x_18_ = lp_Multi_T_Correspondence_exp(v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_epsilon(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&lp_Multi_T_Correspondence_epsilon___closed__0, &lp_Multi_T_Correspondence_epsilon___closed__0_once, _init_lp_Multi_T_Correspondence_epsilon___closed__0);
return v___x_19_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_collapseI___closed__0(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(lp_Multi_T_Correspondence_inaccessible));
v___x_21_ = lp_Multi_T_Correspondence_exp(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_collapseI(void){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_obj_once(&lp_Multi_T_Correspondence_collapseI___closed__0, &lp_Multi_T_Correspondence_collapseI___closed__0_once, _init_lp_Multi_T_Correspondence_collapseI___closed__0);
return v___x_22_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_cardFixed___closed__0(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = ((lean_object*)(lp_Multi_T_Correspondence_inaccessible));
v___x_24_ = lp_Multi_T_Correspondence_card(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_cardFixed(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&lp_Multi_T_Correspondence_cardFixed___closed__0, &lp_Multi_T_Correspondence_cardFixed___closed__0_once, _init_lp_Multi_T_Correspondence_cardFixed___closed__0);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_iterate(lean_object* v_f_26_, lean_object* v_x_27_){
_start:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_x_27_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
lean_dec_ref(v_f_26_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_x_27_, v_one_31_);
lean_inc_ref(v_f_26_);
v___x_33_ = lp_Multi_T_Correspondence_iterate(v_f_26_, v_n_32_);
lean_dec(v_n_32_);
v___x_34_ = lean_apply_1(v_f_26_, v___x_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_iterate___boxed(lean_object* v_f_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_Multi_T_Correspondence_iterate(v_f_35_, v_x_36_);
lean_dec(v_x_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorIdx(lean_object* v_x_38_){
_start:
{
switch(lean_obj_tag(v_x_38_))
{
case 0:
{
lean_object* v___x_39_; 
v___x_39_ = lean_unsigned_to_nat(0u);
return v___x_39_;
}
case 1:
{
lean_object* v___x_40_; 
v___x_40_ = lean_unsigned_to_nat(1u);
return v___x_40_;
}
case 2:
{
lean_object* v___x_41_; 
v___x_41_ = lean_unsigned_to_nat(2u);
return v___x_41_;
}
default: 
{
lean_object* v___x_42_; 
v___x_42_ = lean_unsigned_to_nat(3u);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorIdx___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_Multi_T_Correspondence_Denis_Term_ctorIdx(v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(lean_object* v_t_45_, lean_object* v_k_46_){
_start:
{
if (lean_obj_tag(v_t_45_) == 0)
{
return v_k_46_;
}
else
{
lean_object* v_a_47_; lean_object* v_b_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v_t_45_, 0);
lean_inc(v_a_47_);
v_b_48_ = lean_ctor_get(v_t_45_, 1);
lean_inc(v_b_48_);
lean_dec(v_t_45_);
v___x_49_ = lean_apply_2(v_k_46_, v_a_47_, v_b_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorElim(lean_object* v_motive_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_52_, v_k_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_ctorElim___boxed(lean_object* v_motive_56_, lean_object* v_ctorIdx_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_k_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim(v_motive_56_, v_ctorIdx_57_, v_t_58_, v_h_59_, v_k_60_);
lean_dec(v_ctorIdx_57_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_zero_elim___redArg(lean_object* v_t_62_, lean_object* v_zero_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_62_, v_zero_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_zero_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_zero_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_66_, v_zero_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_add_elim___redArg(lean_object* v_t_70_, lean_object* v_add_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_70_, v_add_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_add_elim(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_add_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_74_, v_add_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_I_elim___redArg(lean_object* v_t_78_, lean_object* v_I_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_78_, v_I_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_I_elim(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_I_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_82_, v_I_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_psi_elim___redArg(lean_object* v_t_86_, lean_object* v_psi_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_86_, v_psi_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_Term_psi_elim(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_psi_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lp_Multi_T_Correspondence_Denis_Term_ctorElim___redArg(v_t_90_, v_psi_92_);
return v___x_93_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
switch(lean_obj_tag(v_x_94_))
{
case 0:
{
if (lean_obj_tag(v_x_95_) == 0)
{
uint8_t v___x_96_; 
v___x_96_ = 1;
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
case 1:
{
lean_object* v_a_98_; lean_object* v_b_99_; uint8_t v___x_100_; 
v_a_98_ = lean_ctor_get(v_x_94_, 0);
v_b_99_ = lean_ctor_get(v_x_94_, 1);
v___x_100_ = 0;
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
return v___x_100_;
}
case 1:
{
lean_object* v_a_101_; lean_object* v_b_102_; uint8_t v_inst_103_; 
v_a_101_ = lean_ctor_get(v_x_95_, 0);
v_b_102_ = lean_ctor_get(v_x_95_, 1);
v_inst_103_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_a_98_, v_a_101_);
if (v_inst_103_ == 0)
{
return v___x_100_;
}
else
{
uint8_t v_inst_104_; 
v_inst_104_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_b_99_, v_b_102_);
if (v_inst_104_ == 0)
{
return v___x_100_;
}
else
{
return v_inst_104_;
}
}
}
default: 
{
return v___x_100_;
}
}
}
case 2:
{
lean_object* v_a_105_; lean_object* v_b_106_; uint8_t v___x_107_; 
v_a_105_ = lean_ctor_get(v_x_94_, 0);
v_b_106_ = lean_ctor_get(v_x_94_, 1);
v___x_107_ = 0;
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
return v___x_107_;
}
case 2:
{
lean_object* v_a_108_; lean_object* v_b_109_; uint8_t v_inst_110_; 
v_a_108_ = lean_ctor_get(v_x_95_, 0);
v_b_109_ = lean_ctor_get(v_x_95_, 1);
v_inst_110_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_a_105_, v_a_108_);
if (v_inst_110_ == 0)
{
return v___x_107_;
}
else
{
uint8_t v_inst_111_; 
v_inst_111_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_b_106_, v_b_109_);
if (v_inst_111_ == 0)
{
return v___x_107_;
}
else
{
return v_inst_111_;
}
}
}
default: 
{
return v___x_107_;
}
}
}
default: 
{
lean_object* v_k_112_; lean_object* v_a_113_; uint8_t v___x_114_; 
v_k_112_ = lean_ctor_get(v_x_94_, 0);
v_a_113_ = lean_ctor_get(v_x_94_, 1);
v___x_114_ = 0;
switch(lean_obj_tag(v_x_95_))
{
case 0:
{
return v___x_114_;
}
case 3:
{
lean_object* v_k_115_; lean_object* v_a_116_; uint8_t v_inst_117_; 
v_k_115_ = lean_ctor_get(v_x_95_, 0);
v_a_116_ = lean_ctor_get(v_x_95_, 1);
v_inst_117_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_k_112_, v_k_115_);
if (v_inst_117_ == 0)
{
return v___x_114_;
}
else
{
uint8_t v_inst_118_; 
v_inst_118_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_a_113_, v_a_116_);
if (v_inst_118_ == 0)
{
return v___x_114_;
}
else
{
return v_inst_118_;
}
}
}
default: 
{
return v___x_114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq___boxed(lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_x_119_, v_x_120_);
lean_dec(v_x_120_);
lean_dec(v_x_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t lp_Multi_T_Correspondence_Denis_instDecidableEqTerm(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm_decEq(v_x_123_, v_x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instDecidableEqTerm___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = lp_Multi_T_Correspondence_Denis_instDecidableEqTerm(v_x_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(2u);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
static lean_object* _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = lean_nat_to_int(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr(lean_object* v_x_155_, lean_object* v_prec_156_){
_start:
{
lean_object* v___y_158_; 
switch(lean_obj_tag(v_x_155_))
{
case 0:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(1024u);
v___x_165_ = lean_nat_dec_le(v___x_164_, v_prec_156_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2);
v___y_158_ = v___x_166_;
goto v___jp_157_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3);
v___y_158_ = v___x_167_;
goto v___jp_157_;
}
}
case 1:
{
lean_object* v_a_168_; lean_object* v_b_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_192_; 
v_a_168_ = lean_ctor_get(v_x_155_, 0);
v_b_169_ = lean_ctor_get(v_x_155_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_192_ == 0)
{
v___x_171_ = v_x_155_;
v_isShared_172_ = v_isSharedCheck_192_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_b_169_);
lean_inc(v_a_168_);
lean_dec(v_x_155_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_192_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___y_175_; uint8_t v___x_189_; 
v___x_173_ = lean_unsigned_to_nat(1024u);
v___x_189_ = lean_nat_dec_le(v___x_173_, v_prec_156_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2);
v___y_175_ = v___x_190_;
goto v___jp_174_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3);
v___y_175_ = v___x_191_;
goto v___jp_174_;
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_176_ = lean_box(1);
v___x_177_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__6));
v___x_178_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_a_168_, v___x_173_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 5);
lean_ctor_set(v___x_171_, 1, v___x_178_);
lean_ctor_set(v___x_171_, 0, v___x_177_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_188_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_176_);
v___x_182_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_b_169_, v___x_173_);
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
lean_inc(v___y_175_);
v___x_184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_184_, 0, v___y_175_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = l_Repr_addAppParen(v___x_186_, v_prec_156_);
return v___x_187_;
}
}
}
}
case 2:
{
lean_object* v_a_193_; lean_object* v_b_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_217_; 
v_a_193_ = lean_ctor_get(v_x_155_, 0);
v_b_194_ = lean_ctor_get(v_x_155_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_217_ == 0)
{
v___x_196_ = v_x_155_;
v_isShared_197_ = v_isSharedCheck_217_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_b_194_);
lean_inc(v_a_193_);
lean_dec(v_x_155_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_217_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___y_200_; uint8_t v___x_214_; 
v___x_198_ = lean_unsigned_to_nat(1024u);
v___x_214_ = lean_nat_dec_le(v___x_198_, v_prec_156_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2);
v___y_200_ = v___x_215_;
goto v___jp_199_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3);
v___y_200_ = v___x_216_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_201_ = lean_box(1);
v___x_202_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__9));
v___x_203_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_a_193_, v___x_198_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 5);
lean_ctor_set(v___x_196_, 1, v___x_203_);
lean_ctor_set(v___x_196_, 0, v___x_202_);
v___x_205_ = v___x_196_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_203_);
v___x_205_ = v_reuseFailAlloc_213_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_201_);
v___x_207_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_b_194_, v___x_198_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
lean_inc(v___y_200_);
v___x_209_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_209_, 0, v___y_200_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = 0;
v___x_211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_210_);
v___x_212_ = l_Repr_addAppParen(v___x_211_, v_prec_156_);
return v___x_212_;
}
}
}
}
default: 
{
lean_object* v_k_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_242_; 
v_k_218_ = lean_ctor_get(v_x_155_, 0);
v_a_219_ = lean_ctor_get(v_x_155_, 1);
v_isSharedCheck_242_ = !lean_is_exclusive(v_x_155_);
if (v_isSharedCheck_242_ == 0)
{
v___x_221_ = v_x_155_;
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_inc(v_k_218_);
lean_dec(v_x_155_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_242_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___y_225_; uint8_t v___x_239_; 
v___x_223_ = lean_unsigned_to_nat(1024u);
v___x_239_ = lean_nat_dec_le(v___x_223_, v_prec_156_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__2);
v___y_225_ = v___x_240_;
goto v___jp_224_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3, &lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3_once, _init_lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__3);
v___y_225_ = v___x_241_;
goto v___jp_224_;
}
v___jp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_226_ = lean_box(1);
v___x_227_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__12));
v___x_228_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_k_218_, v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set_tag(v___x_221_, 5);
lean_ctor_set(v___x_221_, 1, v___x_228_);
lean_ctor_set(v___x_221_, 0, v___x_227_);
v___x_230_ = v___x_221_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_238_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_226_);
v___x_232_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_a_219_, v___x_223_);
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_inc(v___y_225_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___y_225_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = 0;
v___x_236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_235_);
v___x_237_ = l_Repr_addAppParen(v___x_236_, v_prec_156_);
return v___x_237_;
}
}
}
}
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_159_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_instReprTerm_repr___closed__1));
lean_inc(v___y_158_);
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___y_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = 0;
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_161_);
v___x_163_ = l_Repr_addAppParen(v___x_162_, v_prec_156_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_instReprTerm_repr___boxed(lean_object* v_x_243_, lean_object* v_prec_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = lp_Multi_T_Correspondence_Denis_instReprTerm_repr(v_x_243_, v_prec_244_);
lean_dec(v_prec_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_exp(lean_object* v_a_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_omega1));
v___x_261_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_a_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_iterate(lean_object* v_f_273_, lean_object* v_z_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_zero_276_; uint8_t v_isZero_277_; 
v_zero_276_ = lean_unsigned_to_nat(0u);
v_isZero_277_ = lean_nat_dec_eq(v_x_275_, v_zero_276_);
if (v_isZero_277_ == 1)
{
lean_dec_ref(v_f_273_);
lean_inc(v_z_274_);
return v_z_274_;
}
else
{
lean_object* v_one_278_; lean_object* v_n_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_one_278_ = lean_unsigned_to_nat(1u);
v_n_279_ = lean_nat_sub(v_x_275_, v_one_278_);
lean_inc_ref(v_f_273_);
v___x_280_ = lp_Multi_T_Correspondence_Denis_iterate(v_f_273_, v_z_274_, v_n_279_);
lean_dec(v_n_279_);
v___x_281_ = lean_apply_1(v_f_273_, v___x_280_);
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_iterate___boxed(lean_object* v_f_282_, lean_object* v_z_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = lp_Multi_T_Correspondence_Denis_iterate(v_f_282_, v_z_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec(v_z_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_epsilonSeq(lean_object* v_n_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_epsilonSeq___closed__0));
v___x_289_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_one));
v___x_290_ = lp_Multi_T_Correspondence_Denis_iterate(v___x_288_, v___x_289_, v_n_287_);
v___x_291_ = lp_Multi_T_Correspondence_Denis_exp(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_epsilonSeq___boxed(lean_object* v_n_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = lp_Multi_T_Correspondence_Denis_epsilonSeq(v_n_292_);
lean_dec(v_n_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq___lam__0(lean_object* v_b_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_b_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq(lean_object* v_n_298_){
_start:
{
lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___f_299_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_cardFixedSeq___closed__0));
v___x_300_ = lean_box(0);
v___x_301_ = lp_Multi_T_Correspondence_Denis_iterate(v___f_299_, v___x_300_, v_n_298_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_cardFixedSeq___boxed(lean_object* v_n_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = lp_Multi_T_Correspondence_Denis_cardFixedSeq(v_n_302_);
lean_dec(v_n_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq___lam__0(lean_object* v_a_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_I1));
v___x_306_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_a_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq(lean_object* v_n_308_){
_start:
{
lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___f_309_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_collapseISeq___closed__0));
v___x_310_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_one));
v___x_311_ = lp_Multi_T_Correspondence_Denis_iterate(v___f_309_, v___x_310_, v_n_308_);
v___x_312_ = lp_Multi_T_Correspondence_Denis_exp(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_Denis_collapseISeq___boxed(lean_object* v_n_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = lp_Multi_T_Correspondence_Denis_collapseISeq(v_n_313_);
lean_dec(v_n_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_direct(lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
lean_object* v___x_318_; 
v___x_318_ = ((lean_object*)(lp_Multi_T_Correspondence_direct___closed__0));
return v___x_318_;
}
else
{
lean_object* v_s0_319_; lean_object* v_s1_320_; lean_object* v_s2_321_; lean_object* v_s3_322_; lean_object* v_head_324_; lean_object* v___x_338_; uint8_t v___x_348_; 
v_s0_319_ = lean_ctor_get(v_x_317_, 0);
v_s1_320_ = lean_ctor_get(v_x_317_, 1);
v_s2_321_ = lean_ctor_get(v_x_317_, 2);
v_s3_322_ = lean_ctor_get(v_x_317_, 3);
v___x_338_ = lean_box(0);
v___x_348_ = lp_Multi_instDecidableEqT_decEq(v_s0_319_, v___x_338_);
if (v___x_348_ == 0)
{
goto v___jp_349_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lp_Multi_instDecidableEqT_decEq(v_s1_320_, v___x_338_);
if (v___x_354_ == 0)
{
goto v___jp_349_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lp_Multi_T_Correspondence_direct(v_s2_321_);
if (lean_obj_tag(v___x_355_) == 0)
{
if (lean_obj_tag(v___x_355_) == 0)
{
return v___x_355_;
}
else
{
lean_object* v_val_356_; 
v_val_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_356_);
lean_dec_ref_known(v___x_355_, 1);
v_head_324_ = v_val_356_;
goto v___jp_323_;
}
}
else
{
lean_object* v_val_357_; lean_object* v___x_358_; 
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref_known(v___x_355_, 1);
v___x_358_ = lp_Multi_T_Correspondence_Denis_exp(v_val_357_);
v_head_324_ = v___x_358_;
goto v___jp_323_;
}
}
}
v___jp_323_:
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_box(0);
v___x_326_ = lp_Multi_instDecidableEqT_decEq(v_s3_322_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lp_Multi_T_Correspondence_direct(v_s3_322_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_dec(v_head_324_);
return v___x_327_;
}
else
{
lean_object* v_val_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_val_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v_head_324_);
lean_ctor_set(v___x_332_, 1, v_val_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v_head_324_);
return v___x_337_;
}
}
v___jp_339_:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(lp_Multi_T_Correspondence_one));
v___x_341_ = lp_Multi_instDecidableEqT_decEq(v_s0_319_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_box(0);
return v___x_342_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = lp_Multi_instDecidableEqT_decEq(v_s1_320_, v___x_338_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = lp_Multi_instDecidableEqT_decEq(v_s2_321_, v___x_338_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_box(0);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_I1));
v_head_324_ = v___x_347_;
goto v___jp_323_;
}
}
}
}
v___jp_349_:
{
if (v___x_348_ == 0)
{
goto v___jp_339_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(lp_Multi_T_Correspondence_one));
v___x_351_ = lp_Multi_instDecidableEqT_decEq(v_s1_320_, v___x_350_);
if (v___x_351_ == 0)
{
goto v___jp_339_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = lp_Multi_instDecidableEqT_decEq(v_s2_321_, v___x_338_);
if (v___x_352_ == 0)
{
goto v___jp_339_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = ((lean_object*)(lp_Multi_T_Correspondence_Denis_omega1));
v_head_324_ = v___x_353_;
goto v___jp_323_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Multi_T_Correspondence_direct___boxed(lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = lp_Multi_T_Correspondence_direct(v_x_359_);
lean_dec(v_x_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_direct_match__1_splitter___redArg(lean_object* v_x_361_, lean_object* v_h__1_362_, lean_object* v_h__2_363_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec(v_h__2_363_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_apply_1(v_h__1_362_, v___x_364_);
return v___x_365_;
}
else
{
lean_object* v_s0_366_; lean_object* v_s1_367_; lean_object* v_s2_368_; lean_object* v_s3_369_; lean_object* v___x_370_; 
lean_dec(v_h__1_362_);
v_s0_366_ = lean_ctor_get(v_x_361_, 0);
lean_inc(v_s0_366_);
v_s1_367_ = lean_ctor_get(v_x_361_, 1);
lean_inc(v_s1_367_);
v_s2_368_ = lean_ctor_get(v_x_361_, 2);
lean_inc(v_s2_368_);
v_s3_369_ = lean_ctor_get(v_x_361_, 3);
lean_inc(v_s3_369_);
lean_dec_ref_known(v_x_361_, 4);
v___x_370_ = lean_apply_4(v_h__2_363_, v_s0_366_, v_s1_367_, v_s2_368_, v_s3_369_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_direct_match__1_splitter(lean_object* v_motive_371_, lean_object* v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec(v_h__2_374_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_apply_1(v_h__1_373_, v___x_375_);
return v___x_376_;
}
else
{
lean_object* v_s0_377_; lean_object* v_s1_378_; lean_object* v_s2_379_; lean_object* v_s3_380_; lean_object* v___x_381_; 
lean_dec(v_h__1_373_);
v_s0_377_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_s0_377_);
v_s1_378_ = lean_ctor_get(v_x_372_, 1);
lean_inc(v_s1_378_);
v_s2_379_ = lean_ctor_get(v_x_372_, 2);
lean_inc(v_s2_379_);
v_s3_380_ = lean_ctor_get(v_x_372_, 3);
lean_inc(v_s3_380_);
lean_dec_ref_known(v_x_372_, 4);
v___x_381_ = lean_apply_4(v_h__2_374_, v_s0_377_, v_s1_378_, v_s2_379_, v_s3_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___redArg(lean_object* v_x_382_, lean_object* v_h__1_383_, lean_object* v_h__2_384_){
_start:
{
lean_object* v_zero_385_; uint8_t v_isZero_386_; 
v_zero_385_ = lean_unsigned_to_nat(0u);
v_isZero_386_ = lean_nat_dec_eq(v_x_382_, v_zero_385_);
if (v_isZero_386_ == 1)
{
lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_h__2_384_);
v___x_387_ = lean_box(0);
v___x_388_ = lean_apply_1(v_h__1_383_, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v_one_389_; lean_object* v_n_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_383_);
v_one_389_ = lean_unsigned_to_nat(1u);
v_n_390_ = lean_nat_sub(v_x_382_, v_one_389_);
v___x_391_ = lean_apply_1(v_h__2_384_, v_n_390_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___redArg___boxed(lean_object* v_x_392_, lean_object* v_h__1_393_, lean_object* v_h__2_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___redArg(v_x_392_, v_h__1_393_, v_h__2_394_);
lean_dec(v_x_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter(lean_object* v_motive_396_, lean_object* v_x_397_, lean_object* v_h__1_398_, lean_object* v_h__2_399_){
_start:
{
lean_object* v_zero_400_; uint8_t v_isZero_401_; 
v_zero_400_ = lean_unsigned_to_nat(0u);
v_isZero_401_ = lean_nat_dec_eq(v_x_397_, v_zero_400_);
if (v_isZero_401_ == 1)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec(v_h__2_399_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_apply_1(v_h__1_398_, v___x_402_);
return v___x_403_;
}
else
{
lean_object* v_one_404_; lean_object* v_n_405_; lean_object* v___x_406_; 
lean_dec(v_h__1_398_);
v_one_404_ = lean_unsigned_to_nat(1u);
v_n_405_ = lean_nat_sub(v_x_397_, v_one_404_);
v___x_406_ = lean_apply_1(v_h__2_399_, v_n_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter___boxed(lean_object* v_motive_407_, lean_object* v_x_408_, lean_object* v_h__1_409_, lean_object* v_h__2_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = lp_Multi___private_Multi_term3_Term3Correspondence_0__T_Correspondence_iterate_match__1_splitter(v_motive_407_, v_x_408_, v_h__1_409_, v_h__2_410_);
lean_dec(v_x_408_);
return v_res_411_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Multi_Multi_term3_Term3Normal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Multi_Multi_term3_Term3Correspondence(uint8_t builtin) {
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
res = initialize_Multi_Multi_term3_Term3Normal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_Multi_T_Correspondence_uncountable = _init_lp_Multi_T_Correspondence_uncountable();
lean_mark_persistent(lp_Multi_T_Correspondence_uncountable);
lp_Multi_T_Correspondence_epsilon = _init_lp_Multi_T_Correspondence_epsilon();
lean_mark_persistent(lp_Multi_T_Correspondence_epsilon);
lp_Multi_T_Correspondence_collapseI = _init_lp_Multi_T_Correspondence_collapseI();
lean_mark_persistent(lp_Multi_T_Correspondence_collapseI);
lp_Multi_T_Correspondence_cardFixed = _init_lp_Multi_T_Correspondence_cardFixed();
lean_mark_persistent(lp_Multi_T_Correspondence_cardFixed);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
