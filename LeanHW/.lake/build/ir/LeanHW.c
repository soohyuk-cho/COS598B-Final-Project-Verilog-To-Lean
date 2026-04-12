// Lean compiler output
// Module: LeanHW
// Imports: public import Init public import LeanHW.Tier1.Mux_2_1_verA public import LeanHW.Tier1.Mux_2_1_verB public import LeanHW.Tier1.Decoder_2_4_verA public import LeanHW.Tier1.Decoder_2_4_verB public import LeanHW.Tier1.Encoder_4_2_verA public import LeanHW.Tier1.Encoder_4_2_verB public import LeanHW.Tier1.Comparator_4bit_verA public import LeanHW.Tier1.ALU_4_verA public import LeanHW.Tier1.ALU_4_verB public import LeanHW.Tier2.counter_verA public import LeanHW.Tier2.counter_verB
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Mux__2__1__verA(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Mux__2__1__verB(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Decoder__2__4__verA(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Decoder__2__4__verB(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Encoder__4__2__verA(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Encoder__4__2__verB(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_Comparator__4bit__verA(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_ALU__4__verA(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier1_ALU__4__verB(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier2_counter__verA(uint8_t builtin);
lean_object* initialize_LeanHW_LeanHW_Tier2_counter__verB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanHW_LeanHW(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Mux__2__1__verA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Mux__2__1__verB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Decoder__2__4__verA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Decoder__2__4__verB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Encoder__4__2__verA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Encoder__4__2__verB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_Comparator__4bit__verA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_ALU__4__verA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier1_ALU__4__verB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier2_counter__verA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanHW_LeanHW_Tier2_counter__verB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
