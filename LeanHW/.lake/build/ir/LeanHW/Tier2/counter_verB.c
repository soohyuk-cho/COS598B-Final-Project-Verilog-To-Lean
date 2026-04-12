// Lean compiler output
// Module: LeanHW.Tier2.counter_verB
// Imports: public import Init public import Std
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
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_modulus(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_modulus___boxed(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_wrap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_wrap___boxed(lean_object*, lean_object*);
static const lean_string_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__0 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__0_value;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "count"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__1 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__1_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__1_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__2 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__2_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__2_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__3 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__3_value;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__4 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__4_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__4_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__3_value),((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__6 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__6_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__7;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__8 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__8_value;
lean_object* lean_string_length(lean_object*);
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__9;
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__0_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__11 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__11_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__8_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__12 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__12_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState_repr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rst"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__0 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__0_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__0_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__1 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__1_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__1_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__2 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__2_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__2_value),((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__3 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__3_value;
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__4;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__5 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__5_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__5_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__6 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__6_value;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "load"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__7 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__7_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__7_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__8 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__8_value;
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__9;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "en"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__10 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__10_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__10_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__11 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__11_value;
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__12;
static const lean_string_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "loadValue"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__13 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__13_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__13_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__14 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__14_value;
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__15;
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_LeanHW_CounterLoadable_instReprInput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_LeanHW_CounterLoadable_instReprInput_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_LeanHW_CounterLoadable_instReprInput___closed__0 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput___closed__0_value;
LEAN_EXPORT const lean_object* lp_LeanHW_CounterLoadable_instReprInput = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprInput___closed__0_value;
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqInput_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqInput_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqInput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqInput___boxed(lean_object*, lean_object*);
static const lean_string_object lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "countOut"};
static const lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__0 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__0_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__0_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__1 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__1_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__1_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__2 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__2_value;
static const lean_ctor_object lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__2_value),((lean_object*)&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5_value)}};
static const lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__3 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__3_value;
static lean_once_cell_t lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__4;
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_LeanHW_CounterLoadable_instReprOutput___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_LeanHW_CounterLoadable_instReprOutput_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_LeanHW_CounterLoadable_instReprOutput___closed__0 = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput___closed__0_value;
LEAN_EXPORT const lean_object* lp_LeanHW_CounterLoadable_instReprOutput = (const lean_object*)&lp_LeanHW_CounterLoadable_instReprOutput___closed__0_value;
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqOutput_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqOutput_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqOutput(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqOutput___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_zeroState(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_zeroState___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_step___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_modulus(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_modulus___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LeanHW_CounterLoadable_modulus(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_wrap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_modulus(x_1);
x_4 = lean_nat_mod(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_wrap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_LeanHW_CounterLoadable_wrap(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__0));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__9, &lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__9_once, _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__9);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__6));
x_3 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__7, &lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__7_once, _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__7);
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10, &lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10_once, _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10);
x_11 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__11));
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__12));
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_LeanHW_CounterLoadable_instReprState_repr___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_LeanHW_CounterLoadable_instReprState_repr(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_LeanHW_CounterLoadable_instReprState_repr___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_LeanHW_CounterLoadable_instDecidableEqState_decEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqState___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_LeanHW_CounterLoadable_instDecidableEqState(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__5));
x_7 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__3));
x_8 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__4, &lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__4_once, _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__4);
x_9 = l_Bool_repr___redArg(x_2);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__6));
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__8));
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__9, &lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__9_once, _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__9);
x_22 = l_Bool_repr___redArg(x_3);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_11);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
x_28 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__11));
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
x_31 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__12, &lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__12_once, _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__12);
x_32 = l_Bool_repr___redArg(x_4);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_11);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_14);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_16);
x_38 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__14));
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
x_41 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__15, &lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__15_once, _init_lp_LeanHW_CounterLoadable_instReprInput_repr___redArg___closed__15);
x_42 = l_Nat_reprFast(x_5);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_11);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10, &lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10_once, _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10);
x_48 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__11));
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__12));
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_11);
return x_53;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_LeanHW_CounterLoadable_instReprInput_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprInput_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_LeanHW_CounterLoadable_instReprInput_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqInput_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_10 = lean_ctor_get(x_2, 0);
if (x_3 == 0)
{
if (x_7 == 0)
{
goto block_14;
}
else
{
return x_3;
}
}
else
{
if (x_7 == 0)
{
return x_7;
}
else
{
goto block_14;
}
}
block_13:
{
if (x_5 == 0)
{
if (x_9 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_6, x_10);
return x_11;
}
else
{
return x_5;
}
}
else
{
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_6, x_10);
return x_12;
}
}
}
block_14:
{
if (x_4 == 0)
{
if (x_8 == 0)
{
goto block_13;
}
else
{
return x_4;
}
}
else
{
if (x_8 == 0)
{
return x_8;
}
else
{
goto block_13;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqInput_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqInput_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqInput(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqInput_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqInput___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqInput(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__3));
x_3 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__4, &lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__4_once, _init_lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg___closed__4);
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_obj_once(&lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10, &lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10_once, _init_lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__10);
x_11 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__11));
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = ((lean_object*)(lp_LeanHW_CounterLoadable_instReprState_repr___redArg___closed__12));
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_LeanHW_CounterLoadable_instReprOutput_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instReprOutput_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_LeanHW_CounterLoadable_instReprOutput_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqOutput_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqOutput_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqOutput_decEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_LeanHW_CounterLoadable_instDecidableEqOutput(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_instDecidableEqOutput___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_LeanHW_CounterLoadable_instDecidableEqOutput(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_zeroState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_zeroState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LeanHW_CounterLoadable_zeroState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_step(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
if (x_6 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lp_LeanHW_CounterLoadable_wrap(x_1, x_8);
lean_dec(x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lp_LeanHW_CounterLoadable_wrap(x_1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(0u);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_step___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_LeanHW_CounterLoadable_step(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LeanHW_CounterLoadable_out___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LeanHW_CounterLoadable_out___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_LeanHW_CounterLoadable_out(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Std(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanHW_LeanHW_Tier2_counter__verB(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
