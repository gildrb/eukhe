
// Imports
// =======

// The Objective-C headers take #include, not #import: a build
// (-o) reads an #import as the framework of an effect.

#pragma clang fp contract(off)

#ifdef __CUDACC_RTC__
#define BEND_RTC 1
#endif

#ifdef __METAL_VERSION__
#include <metal_stdlib>
using namespace metal;
#elif !BEND_RTC
#ifdef __APPLE__
#define _DARWIN_UNLIMITED_SELECT
#else
#define _GNU_SOURCE
#endif
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <unistd.h>
#include <signal.h>
#include <sys/mman.h>
#include <time.h>
#include <poll.h>
#include <sys/select.h>
#include <fcntl.h>
#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif
#ifdef __OBJC__
#include <Metal/Metal.h>
#include <Foundation/Foundation.h>
#elif BEND_CUDA
#include <cuda.h>
#include <nvrtc.h>
#include <sys/stat.h>
#endif
#endif

// Dialect
// =======

// Metal needs coherent(device) (MSL 3.2), or M1-class parts lose stores
// across threadgroups; CUDA lanes hand off through a32 and FENCE. The
// preserve_* attributes need clang 19+ and an optimized build. A segment is
// a case of the device's switch, or a host preserve_none function entered
// by musttail.

#ifdef __METAL_VERSION__
#if __METAL_VERSION__ >= 320
#define DEV     coherent(device) device
#else
#define DEV     device
#endif
#define THR     thread
#define TG      threadgroup
#define INLINE  inline
#define OUTLINE static
#define CONSTV  constant
#define DEVICE  1
#define CLZ(x)  clz(x)
#define FENCE() atomic_thread_fence(mem_flags::mem_device, memory_order_seq_cst)
#define BAR()   threadgroup_barrier(mem_flags::mem_threadgroup)
#define BARD()  threadgroup_barrier(mem_flags::mem_device \
  | mem_flags::mem_threadgroup)
#else
#define DEV
#define THR
#define TG
#define INLINE  static inline
#define CONSTV  static const
#ifdef BEND_RTC
#define OUTLINE FAR
#define DEVICE  1
#define CLZ(x)  (u32)__clz((int)(x))
#define FENCE() __threadfence()
#define BAR()   __syncthreads()
#define BARD()  { __threadfence(); __syncthreads(); }
#else
#if __has_attribute(preserve_none) && __has_attribute(preserve_most) \
  && __OPTIMIZE__
#define PRESERVE(A) __attribute__((A))
#else
#define PRESERVE(A)
#endif
#define OUTLINE FAR __attribute__((cold)) PRESERVE(preserve_most)
#define DEVICE  0
#define CLZ(x)  (u32)__builtin_clz(x)
#define FENCE() ((void)0)
#endif
#endif
#define FAR static __attribute__((noinline))

// The device inlines a spin once per caller, so a long one is a call there.
// The host lets clang decide.
#if DEVICE
#define DFAR       FAR
#define LOCK(l)
#define UNLOCK(l)
#define WL_CASE(F) case F: {
#define WL_OPEN    {
#define WL_JMP(F)  { fid = (F); break; }
#define WL_DYN     WL_JMP
#else
#define DFAR       INLINE
#define LOCK(l)    while (__atomic_exchange_n(&(l), 1, __ATOMIC_ACQUIRE)) {}
#define UNLOCK(l)  __atomic_store_n(&(l), 0, __ATOMIC_RELEASE)
#define WL_FN      FAR PRESERVE(preserve_none) Term
#define WL_CASE(F) WL_FN WL_##F(WL_SIG) {
#define WL_OPEN    { WL_BANK u32 rn;
#define WL_JMP(F)  __attribute__((musttail)) return WL_##F(WL_ALL)
#define WL_DYN(F)  __attribute__((musttail)) return wl_tab[F](WL_ALL)
#endif
#define WL_SPIN     for (;;) { if (err_spun(e.mem, &wpoll)) { return 0; }
#define WL_SPUN     } break;
#define WL_AGAIN(F) continue

#define LANE_STEP (DEVICE ? (long)CUBE : 1)
#define STK(I)    sp[(long)(I) * LANE_STEP]

#define WL_RETN(N)  { rn = (N); sp -= LANE_STEP; WL_DYN((u32)STK(0)); }
#define WL_CONT     STK(-3)
#define WL_IDX      STK(-2)
#define WL_POPN(N)  sp -= (N) * LANE_STEP
#define WL_PUSHN(N) sp += (N) * LANE_STEP
#define WL_FRAME(T) \
  u64 wtl = task_tail(T); \
  STK(0) = e.mem[wtl]; \
  STK(1) = (e.mem[wtl + 1] >> 32) & 0xFFFF; \
  STK(2) = FID_EXIT; \
  WL_PUSHN(3);
#define WL_ARGS(A, N) \
  for (u32 wi = 0; wi < (N); wi += 1) { \
    STK(wi) = e.mem[(A) + wi]; \
  } \
  WL_PUSHN(N);
#define WL_ROOM(N, D) \
  if (DEVICE && sp + (N) * CUBE >= e.mem + STAT_OFF + CUBE \
    && !(sp = lane_spill(e, sp, N, D))) { \
    err_post(e.mem, ERR_DEEP); \
    return 0; \
  }

// Types
// =====

#ifdef __METAL_VERSION__
typedef ulong u64;
typedef uint  u32;
typedef uchar u8;
#elif BEND_RTC
typedef unsigned long long u64;
typedef unsigned int       u32;
typedef unsigned char      u8;
#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
#endif
typedef unsigned short u16;
typedef float f32;

typedef u64 Term;

typedef struct {
  DEV u64* mem;
  DEV u64* alc;
} Env;

typedef struct {
  u64 off;
  u32 rd;
  u32 wr;
  u32 top;
} Bank;

#if DEVICE
typedef u32 u32a;
#else
typedef u32 __attribute__((may_alias)) u32a;
#endif

// Constants
// =========

#define TAG_PAK 1ull
#define TAG_CTR 2ull
#define TAG_CLO 3ull
#define TAG_BUF 4ull
#define TAG_TSK 5ull
#define TAG_ARR 6ull

#define TERM_HOLE (~0ull)
#define LOC_MASK  ((1ull << 40) - 1)
#define RFC_BIT   (1ull << 63)
#define RFC_CNT   ((1u << 24) - 1)
#define NAT_IMM   ((1ull << 48) - 1)

enum { ERR_RING = 1, ERR_TAGS, ERR_HEAP, ERR_FIDS, ERR_NATS, ERR_RFCS,
  ERR_DEEP, ERR_ARRS, ERR_CNTS };

#define LINE      16
#define PAGE_BITS 7
#define PAGE_LEN  (1ull << PAGE_BITS)
#define CUBE_T    128
#define CUBE      ((u64)CUBE_T * CUBE_T)
#define CUBE_G    (1u << CUBE_LOG)
#define LANES     ((u64)CUBE_T << CUBE_LOG)
#define RING_LEN  (1ull << (17 - CUBE_LOG))
#define STAK_LEN  (1ull << 11)
#define NCLS      8
#define NCLS_ALL  32
#define IO_HELP   64

#define TG_HOLD   2304
#define CHUNK     256
#define CAP_WORDS 32768
#define QUANTUM   (DEVICE ? PAGE_LEN \
  : KEEP_WORDS < 32 * PAGE_LEN ? KEEP_WORDS : 32 * PAGE_LEN)
#if DEVICE
#define KEEP_WORDS CHUNK
#endif
#define RING_WORDS ((1ull << 10) + 2)

#define H_BUMP       0
#define H_CAP        1
#define H_CURSOR     LINE
#define H_FRONT      (H_CURSOR + 1)
#define H_GROUPS     (H_CURSOR + 2)
#define H_ROOT_DONE  (2 * LINE)
#define H_ERROR_CODE (3 * LINE)
#define H_ROOT_WORD  (4 * LINE)
#define H_BANK       (H_ROOT_WORD + WL_RESW)

#define PAGE_UP(n) (((n) + PAGE_LEN - 1) & ~(PAGE_LEN - 1))
#define ALC_OFF  PAGE_UP(H_BANK + 3 * NCLS_ALL)
#define RING_OFF (ALC_OFF + CUBE * 2 * NCLS_ALL)
#define STAK_OFF (RING_OFF + CUBE * RING_WORDS)
#define STAT_OFF (STAK_OFF + CUBE * STAK_LEN)
#define HEAP_OFF (STAT_OFF + PAGE_UP(STAT_LEN))

// Globals
// =======

// The bag is 2^CUBE_LOG groups of CUBE_T lanes (a -D constant on the
// device). The device program compiles from the binary's own text.

#if !DEVICE

static u64*    CORPUS;
static u64    ALC[CUBE_T + 1][3 * NCLS_ALL] __attribute__((aligned(128)));
static u32    KEEP_WORDS;
static u32    CUBE_LOG = 7;
static u32    bank_lock;

static u32             pool_size;
static u32             pool_row;
static u32             pool_done;
static pthread_mutex_t pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  pool_wake = PTHREAD_COND_INITIALIZER;
static pthread_cond_t  pool_join = PTHREAD_COND_INITIALIZER;

#if BEND_METAL || BEND_CUDA
#pragma clang diagnostic ignored "-Wc23-extensions"
static const char BEND_SRC[] = {
#embed __FILE__
, 0 };
#endif

#ifdef __OBJC__
static id<MTLDevice>               gpu_dev;
static id<MTLCommandQueue>         gpu_que;
static id<MTLComputePipelineState> gpu_pso;
static id<MTLBuffer>               gpu_buf;
static id<MTLComputeCommandEncoder> gpu_enc;
#elif BEND_CUDA
static CUdevice   gpu_dev;
static CUmodule   gpu_lib;
static CUfunction gpu_pso;
#endif
static bool io_gpu;
static DEV Term*  io_stk;

static const char* CLI_HELP =
  "usage: %s [+RTS options -RTS] [arguments]\n"
  "  --threads N       worker threads, 1 to 128 (default: the CPU count)\n"
  "  --gpu on|off|4GB  run ! calls on the GPU, over this much of its memory\n"
  "                    (default: on if present, over 2GB on Metal)\n"
  "  --gpu-build       write the GPU program and exit\n"
  "  --help            show this text\n";

#endif

// Tables
// ======

typedef struct { u8 ar, resw, bangs, nofk; } Fid;
typedef struct { u8 ar, hot; u16 spine; } Cid;

#define CID_Tuple 0
#define CID_SNil 1
#define CID_SCon 2
#define CID_WCon 3
#define CID_Emit 4
#define CID_Halt 5
#define CID_Exit 6
#define CID_Fail 7
#define CID_Done 8
#define CID_Ready 9
#define CID_Wait 10
#define CID_None 11
#define CID_Some 12
#define CID_False 13
#define CID_True 14
#define CID_Unit 15
#define CID_Nil 16
#define CID_Con 17
#define CID_Chr 18
#define CID_Echo 19
#define CID_Cvar 20
#define CID_Unknown 21
#define CID_LT 22
#define CID_EQ 23
#define CID_GT 24
#define CID_ffi_echo_Echo 25
#define CID_ffi_echo_Refused 26
#define CID_ffi_cvar_Table 27
#define CID_ffi_cvar_Refused 28
#define CID_cvar_KeyBind 29
#define CID_cvar_Alias 30
#define CID_WNil 31
#define CID_cvar_CSet 32
#define CID_cvar_CToggle 33
#define CID_cvar_CRun 34
#define CID_cvar_CGone 35
#define CID_wire_Got 36
#define CID_wire_Bad 37
#define CID_cvar_VNat 38
#define CID_cvar_VBool 39
#define CID_ffi_director_Req 40
#define CID_ffi_child_env_Req 41
#define CID_ffi_cvar_Xreq 42
#define CID_director_Loop 43
#define CID_director_Defer 44
#define CID_director_Again 45
#define CID_director_Yield 46
#define CID_director_Stack 47
#define CID_director_Leave 48
#define CID_director_Abort 49
#define CID_director_Lead 50
#define CID_child_env_Var 51
#define CID_wire_Dig 52
#define CID_wire_Comma 53
#define CID_wire_Other 54
#define CID_cvar_Flat 55
#define CID_cvar_Cycle 56
#define CID_cvar_Unknown 57
#define CID_director_Layer 58
#define CID_director_Cont 59
#define CID_director_Hand 60
#define CID_director_Failed 61
#define CID_director_Dec 62
#define CID_IO_args 63
#define CID_IO_print 64
#define FID_String_starts_with_go 0
#define FID_String_starts_with 1
#define FID_ffi_cvar_get_val 2
#define FID_ffi_cvar_get_val_k12 3
#define FID_ffi_cvar_get_val_k13 4
#define FID_String_contains 5
#define FID_String_contains_k16 6
#define FID_child_env_matched_at 7
#define FID_child_env_matched_go 8
#define FID_child_env_matched_go_k26 9
#define FID_child_env_matched 10
#define FID_child_env_matched_k47 11
#define FID_wire_get_list_go_7 12
#define FID_wire_get_list_go_7_k69 13
#define FID_wire_get_list_go_7_k70 14
#define FID_wire_put_list_go_7 15
#define FID_wire_put_list_go_7_k72 16
#define FID_wire_put_str_go 17
#define FID_wire_put_str_go_k74 18
#define FID_child_env_named 19
#define FID_child_env_named_k80 20
#define FID_child_env_up 21
#define FID_child_env_up_k86 22
#define FID_ffi_child_env_put_var 23
#define FID_ffi_child_env_put_var_k88 24
#define FID_ffi_director_get_layer 25
#define FID_ffi_director_get_layer_k90 26
#define FID_ffi_director_get_layer_k91 27
#define FID_wire_get_list_go_5 28
#define FID_wire_get_list_go_5_k93 29
#define FID_wire_get_list_go_5_k94 30
#define FID_director_decide_go 31
#define FID_director_decide_go_k100 32
#define FID_director_decide_go_k101 33
#define FID_director_decide_go_k102 34
#define FID_ffi_cvar_get_cmd 35
#define FID_ffi_cvar_get_cmd_k110 36
#define FID_ffi_cvar_get_cmd_k111 37
#define FID_ffi_cvar_get_cmd_k112 38
#define FID_ffi_cvar_get_cmd_k113 39
#define FID_ffi_cvar_get_cmd_k114 40
#define FID_ffi_cvar_get_cmd_k115 41
#define FID_wire_get_list_go_2 42
#define FID_wire_get_list_go_2_k117 43
#define FID_wire_get_list_go_2_k118 44
#define FID_wire_put_list_7 45
#define FID_wire_put_list_7_k122 46
#define FID_wire_put_str 47
#define FID_wire_put_str_k124 48
#define FID_wire_take 49
#define FID_wire_take_k128 50
#define FID_ffi_child_env_get_var 51
#define FID_ffi_child_env_get_var_k130 52
#define FID_ffi_child_env_get_var_k131 53
#define FID_wire_get_list_go_0 54
#define FID_wire_get_list_go_0_k133 55
#define FID_wire_get_list_go_0_k134 56
#define FID_child_env_under 57
#define FID_child_env_under_k136 58
#define FID_child_env_under_k137 59
#define FID_List_append 60
#define FID_List_append_k139 61
#define FID_child_env_passes 62
#define FID_child_env_passes_k142 63
#define FID_child_env_passes_k143 64
#define FID_ffi_director_get_end 65
#define FID_ffi_director_get_end_k150 66
#define FID_ffi_director_get_end_k151 67
#define FID_ffi_director_get_verdict 68
#define FID_ffi_director_get_verdict_k154 69
#define FID_ffi_director_get_verdict_k155 70
#define FID_wire_get_list_go_6 71
#define FID_wire_get_list_go_6_k157 72
#define FID_wire_get_list_go_6_k158 73
#define FID_director_decide_as 74
#define FID_director_decide_as_k160 75
#define FID_director_kept 76
#define FID_director_kept_k162 77
#define FID_wire_put_list_go_5 78
#define FID_wire_put_list_go_5_k167 79
#define FID_wire_put_list_go_2 80
#define FID_wire_put_list_go_2_k172 81
#define FID_wire_value 82
#define FID_wire_value_k182 83
#define FID_wire_get_list_7 84
#define FID_wire_get_list_7_k185 85
#define FID_wire_get_list_7_k186 86
#define FID_child_env_merge 87
#define FID_child_env_merge_k195 88
#define FID_child_env_keep 89
#define FID_child_env_keep_k197 90
#define FID_child_env_keep_k198 91
#define FID_wire_put_list_go_1 92
#define FID_wire_put_list_go_1_k200 93
#define FID_wire_put_list_go_1_k201 94
#define FID_wire_get_list_5 95
#define FID_wire_get_list_5_k204 96
#define FID_wire_get_list_5_k205 97
#define FID_director_decide 98
#define FID_wire_put_list_5 99
#define FID_wire_put_list_5_k217 100
#define FID_List_length 101
#define FID_List_length_k225 102
#define FID_cvar_expand_go 103
#define FID_cvar_expand_go_k227 104
#define FID_ffi_cvar_get_alias 105
#define FID_ffi_cvar_get_alias_k236 106
#define FID_ffi_cvar_get_alias_k237 107
#define FID_wire_get_list_go_3 108
#define FID_wire_get_list_go_3_k239 109
#define FID_wire_get_list_go_3_k240 110
#define FID_wire_cdig_go 111
#define FID_wire_cdig_go_k246 112
#define FID_wire_get_nat_go 113
#define FID_wire_get_nat_go_k249 114
#define FID_wire_get_nat_go_k250 115
#define FID_wire_get_nat_end 116
#define FID_wire_get_nat_end_k252 117
#define FID_wire_get_str 118
#define FID_wire_get_str_k261 119
#define FID_wire_get_list_go_1 120
#define FID_wire_get_list_go_1_k263 121
#define FID_wire_get_list_go_1_k264 122
#define FID_wire_get_list_0 123
#define FID_wire_get_list_0_k266 124
#define FID_wire_get_list_0_k267 125
#define FID_child_env_child 126
#define FID_child_env_child_k271 127
#define FID_wire_get_list_6 128
#define FID_wire_get_list_6_k278 129
#define FID_wire_get_list_6_k279 130
#define FID_director_tick 131
#define FID_director_tick_k282 132
#define FID_director_tick_k283 133
#define FID_director_tick_k284 134
#define FID_director_tick_k285 135
#define FID_ffi_cvar_get_bind 136
#define FID_ffi_cvar_get_bind_k289 137
#define FID_ffi_cvar_get_bind_k290 138
#define FID_wire_get_list_go_4 139
#define FID_wire_get_list_go_4_k292 140
#define FID_wire_get_list_go_4_k293 141
#define FID_U32_show_go 142
#define FID_cvar_expand 143
#define FID_cvar_expand_k297 144
#define FID_cvar_expand_k298 145
#define FID_ffi_cvar_put_cmds 146
#define FID_ffi_cvar_put_cmds_k300 147
#define FID_ffi_cvar_get_cmds 148
#define FID_ffi_cvar_get_cmds_k306 149
#define FID_ffi_cvar_get_cmds_k307 150
#define FID_wire_tok 151
#define FID_wire_tok_k312 152
#define FID_ffi_director_get_loop 153
#define FID_ffi_director_get_loop_k330 154
#define FID_ffi_director_get_loop_k331 155
#define FID_ffi_director_get_loop_k332 156
#define FID_cvar_press 157
#define FID_ffi_cvar_put_exp 158
#define FID_ffi_cvar_put_exp_k345 159
#define FID_Nat_show_fin 160
#define FID_wire_get_list_3 161
#define FID_wire_get_list_3_k349 162
#define FID_wire_get_list_3_k350 163
#define FID_wire_peek 164
#define FID_wire_peek_k356 165
#define FID_wire_get_u32 166
#define FID_wire_get_u32_k361 167
#define FID_wire_get_list_1 168
#define FID_wire_get_list_1_k368 169
#define FID_wire_get_list_1_k369 170
#define FID_wire_get_list_4 171
#define FID_wire_get_list_4_k384 172
#define FID_wire_get_list_4_k385 173
#define FID_U32_show 174
#define FID_Nat_show 175
#define FID_String_append 176
#define FID_String_append_k396 177
#define FID_ffi_cvar_get_xreq 178
#define FID_ffi_cvar_get_xreq_k398 179
#define FID_ffi_cvar_get_xreq_k399 180
#define FID_wire_get_nat 181
#define FID_wire_get_nat_k403 182
#define FID_wire_get_nat_k404 183
#define FID_ffi_child_env_get_req 184
#define FID_ffi_child_env_get_req_k412 185
#define FID_ffi_child_env_get_req_k413 186
#define FID_ffi_child_env_get_req_k414 187
#define FID_ffi_child_env_get_req_k415 188
#define FID_ffi_director_get_req 189
#define FID_ffi_director_get_req_k420 190
#define FID_ffi_director_get_req_k421 191
#define FID_ffi_director_get_req_k422 192
#define FID_ffi_cvar_get_table 193
#define FID_ffi_cvar_get_table_k427 194
#define FID_ffi_cvar_get_table_k428 195
#define FID_ffi_cvar_step 196
#define FID_ffi_cvar_step_k433 197
#define FID_ffi_cvar_step_k434 198
#define FID_ffi_cvar_step_k435 199
#define FID_ffi_echo_step 200
#define FID_ffi_echo_step_k438 201
#define FID_ffi_echo_step_k439 202
#define FID_ffi_echo_step_k440 203
#define FID_ffi_cvar_open 204
#define FID_ffi_cvar_open_k462 205
#define FID_ffi_echo_open 206
#define FID_ffi_echo_open_k466 207
#define FID_ffi_echo_open_k467 208
#define FID_step_go 209
#define FID_step_go_k470 210
#define FID_step_go_k471 211
#define FID_ffi_go 212
#define FID_ffi_go_k474 213
#define FID_ffi_go_k475 214
#define FID_ffi_go_k476 215
#define FID_ffi_go_k477 216
#define FID_ffi_go_k478 217
#define FID_ffi_go_k479 218
#define FID_ffi_go_k480 219
#define FID_ffi_go_k481 220
#define FID_ffi_go_k482 221
#define FID_ffi_go_k483 222
#define FID_ffi_go_k484 223
#define FID_ffi_go_k485 224
#define FID_ffi_go_k486 225
#define FID_ffi_go_k487 226
#define FID_open_go 227
#define FID_open_go_k491 228
#define FID_open_go_k492 229
#define FID_step 230
#define FID_step_k494 231
#define FID_close 232
#define FID_ffi 233
#define FID_ffi_k498 234
#define FID_U32_read_go 235
#define FID_open 236
#define FID_open_k503 237
#define FID_cli_steps 238
#define FID_cli_steps_k505 239
#define FID_cli_steps_k506 240
#define FID_cli_steps_k507 241
#define FID_U32_read 242
#define FID_cli_print 243
#define FID_cli_print_c519 244
#define FID_cli_print_c520 245
#define FID_cli_print_c521 246
#define FID_cli_args 247
#define FID_cli_args_k523 248
#define FID_cli_args_k524 249
#define FID_cli_args_k525 250
#define FID_cli_args_k526 251
#define FID_IO_bind 252
#define FID_IO_bind_c530 253
#define FID_IO_bind_k531 254
#define FID_main 255
#define FID_main_c533 256
#define FID_main_c534 257
#define FID_main_k535 258
#define FID_main_c536 259
#define FID_IO_args 260
#define FID_IO_print 261
#define FID_IO_emit 262
#define FID_Clo_apply 263
#define FID_EXIT 264
#define FID_ENTER 265
CONSTV Fid FID_T[] = { { 2, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 4, 0, 0, 1 }, { 5, 3, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 3, 2, 0, 1 }, { 2, 0, 0, 1 }, { 3, 2, 0, 1 }, { 2, 0, 0, 1 }, { 4, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 3, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 7, 4, 0, 1 }, { 5, 3, 0, 1 }, { 4, 0, 0, 1 }, { 4, 2, 0, 1 }, { 4, 2, 0, 1 }, { 5, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 7, 0, 0, 1 }, { 11, 6, 0, 1 }, { 7, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 7, 4, 0, 1 }, { 5, 3, 0, 1 }, { 2, 0, 0, 1 }, { 5, 1, 0, 1 }, { 4, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 3, 0, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 6, 0, 0, 1 }, { 9, 5, 0, 1 }, { 6, 3, 0, 1 }, { 4, 0, 0, 1 }, { 5, 1, 0, 1 }, { 3, 0, 0, 1 }, { 3, 2, 0, 1 }, { 2, 0, 0, 1 }, { 4, 2, 0, 1 }, { 2, 0, 0, 1 }, { 6, 2, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 3, 0, 0, 1 }, { 6, 1, 0, 1 }, { 4, 1, 0, 1 }, { 2, 0, 0, 1 }, { 4, 2, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 1, 1, 0, 1 }, { 5, 0, 0, 1 }, { 5, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 7, 4, 0, 1 }, { 5, 3, 0, 1 }, { 3, 0, 0, 1 }, { 5, 2, 0, 1 }, { 5, 0, 0, 1 }, { 6, 3, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 0, 0, 1 }, { 5, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 4, 0, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 6, 5, 0, 1 }, { 6, 0, 0, 1 }, { 6, 2, 0, 1 }, { 1, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 7, 4, 0, 1 }, { 5, 3, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 7, 6, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 6, 4, 0, 1 }, { 3, 0, 0, 1 }, { 3, 0, 0, 1 }, { 1, 1, 0, 1 }, { 4, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 3, 0, 1 }, { 6, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 7, 6, 0, 1 }, { 8, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 4, 0, 0, 1 }, { 5, 3, 0, 1 }, { 4, 2, 0, 1 }, { 3, 1, 0, 1 }, { 4, 0, 0, 1 }, { 4, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 5, 5, 0, 1 }, { 1, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 1, 0, 1 }, { 5, 0, 0, 1 }, { 4, 4, 0, 1 }, { 4, 4, 0, 1 }, { 2, 0, 0, 1 }, { 8, 8, 0, 1 }, { 4, 4, 0, 1 }, { 2, 1, 0, 1 }, { 6, 6, 0, 1 }, { 1, 1, 0, 1 }, { 2, 2, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 6, 3, 0, 1 }, { 7, 3, 0, 1 }, { 5, 1, 0, 1 }, { 4, 1, 0, 1 }, { 4, 4, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 4, 4, 0, 1 }, { 4, 4, 0, 1 }, { 5, 0, 0, 1 }, { 5, 5, 0, 1 }, { 4, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 0, 0, 1 }, { 5, 5, 0, 1 }, { 6, 0, 0, 1 }, { 2, 1, 0, 1 }, { 7, 5, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 5, 2, 0, 1 }, { 1, 1, 0, 1 }, { 6, 5, 0, 1 }, { 1, 1, 0, 1 }, { 3, 0, 0, 1 }, { 3, 0, 0, 1 }, { 2, 1, 0, 1 }, { 0, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 } };
CONSTV Cid CID_T[] = { { 2, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 2, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 1, 1, 0 }, { 3, 0, 0 }, { 3, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 2, 1, 0 }, { 2, 1, 0 }, { 0, 0, 0 }, { 3, 1, 0 }, { 1, 1, 0 }, { 1, 1, 0 }, { 1, 1, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 1, 1, 0 }, { 1, 1, 0 }, { 6, 0, 0 }, { 4, 0, 0 }, { 2, 0, 0 }, { 4, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 2, 1, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 1, 0, 0 }, { 2, 0, 0 } };
#define STAT_LEN 856

#define WL_RESW 8
#define BANGS   0

#define WL_BANK Term r0, r1, r2, r3, r4, r5, rp, r6, r7;

#define WL_LOAD(A, N) \
  do { \
    if ((N) <= 0) break; r0 = e.mem[(A) + 0]; \
    if ((N) <= 1) break; r1 = e.mem[(A) + 1]; \
    if ((N) <= 2) break; r2 = e.mem[(A) + 2]; \
    if ((N) <= 3) break; r3 = e.mem[(A) + 3]; \
    if ((N) <= 4) break; r4 = e.mem[(A) + 4]; \
    if ((N) <= 5) break; r5 = e.mem[(A) + 5]; \
    if ((N) <= 6) break; r6 = e.mem[(A) + 6]; \
    if ((N) <= 7) break; r7 = e.mem[(A) + 7]; \
  } while (0);

#define WL_LAST(X) \
  switch (war) { \
    case 0: r0 = (X); \
      break; \
    case 1: r1 = (X); \
      break; \
    case 2: r2 = (X); \
      break; \
    case 3: r3 = (X); \
      break; \
    case 4: r4 = (X); \
      break; \
    case 5: r5 = (X); \
      break; \
    case 6: r6 = (X); \
      break; \
    case 7: r7 = (X); \
      break; \
  }

#define WL_SAVE(V) (V)[0] = r0; (V)[1] = r1; (V)[2] = r2; (V)[3] = r3; (V)[4] = r4; (V)[5] = r5; (V)[6] = r6; (V)[7] = r7;

#define WL_TAKE(V) r0 = (V)[0]; r1 = (V)[1]; r2 = (V)[2]; r3 = (V)[3]; r4 = (V)[4]; r5 = (V)[5]; r6 = (V)[6]; r7 = (V)[7];

#define WL_SIG Env e, DEV Term* sp, u32 seq, u32 rn, Term r0, Term r1, Term r2, Term r3, Term r4, Term r5, Term rp, Term r6, Term r7

#define WL_ALL e, sp, seq, rn, r0, r1, r2, r3, r4, r5, rp, r6, r7

#define WL_TABLE WL_X(FID_String_starts_with_go) WL_X(FID_String_starts_with) WL_X(FID_ffi_cvar_get_val) WL_X(FID_ffi_cvar_get_val_k12) WL_X(FID_ffi_cvar_get_val_k13) WL_X(FID_String_contains) WL_X(FID_String_contains_k16) WL_X(FID_child_env_matched_at) WL_X(FID_child_env_matched_go) WL_X(FID_child_env_matched_go_k26) WL_X(FID_child_env_matched) WL_X(FID_child_env_matched_k47) WL_X(FID_wire_get_list_go_7) WL_X(FID_wire_get_list_go_7_k69) WL_X(FID_wire_get_list_go_7_k70) WL_X(FID_wire_put_list_go_7) WL_X(FID_wire_put_list_go_7_k72) WL_X(FID_wire_put_str_go) WL_X(FID_wire_put_str_go_k74) WL_X(FID_child_env_named) WL_X(FID_child_env_named_k80) WL_X(FID_child_env_up) WL_X(FID_child_env_up_k86) WL_X(FID_ffi_child_env_put_var) WL_X(FID_ffi_child_env_put_var_k88) WL_X(FID_ffi_director_get_layer) WL_X(FID_ffi_director_get_layer_k90) WL_X(FID_ffi_director_get_layer_k91) WL_X(FID_wire_get_list_go_5) WL_X(FID_wire_get_list_go_5_k93) WL_X(FID_wire_get_list_go_5_k94) WL_X(FID_director_decide_go) WL_X(FID_director_decide_go_k100) WL_X(FID_director_decide_go_k101) WL_X(FID_director_decide_go_k102) WL_X(FID_ffi_cvar_get_cmd) WL_X(FID_ffi_cvar_get_cmd_k110) WL_X(FID_ffi_cvar_get_cmd_k111) WL_X(FID_ffi_cvar_get_cmd_k112) WL_X(FID_ffi_cvar_get_cmd_k113) WL_X(FID_ffi_cvar_get_cmd_k114) WL_X(FID_ffi_cvar_get_cmd_k115) WL_X(FID_wire_get_list_go_2) WL_X(FID_wire_get_list_go_2_k117) WL_X(FID_wire_get_list_go_2_k118) WL_X(FID_wire_put_list_7) WL_X(FID_wire_put_list_7_k122) WL_X(FID_wire_put_str) WL_X(FID_wire_put_str_k124) WL_X(FID_wire_take) WL_X(FID_wire_take_k128) WL_X(FID_ffi_child_env_get_var) WL_X(FID_ffi_child_env_get_var_k130) WL_X(FID_ffi_child_env_get_var_k131) WL_X(FID_wire_get_list_go_0) WL_X(FID_wire_get_list_go_0_k133) WL_X(FID_wire_get_list_go_0_k134) WL_X(FID_child_env_under) WL_X(FID_child_env_under_k136) WL_X(FID_child_env_under_k137) WL_X(FID_List_append) WL_X(FID_List_append_k139) WL_X(FID_child_env_passes) WL_X(FID_child_env_passes_k142) WL_X(FID_child_env_passes_k143) WL_X(FID_ffi_director_get_end) WL_X(FID_ffi_director_get_end_k150) WL_X(FID_ffi_director_get_end_k151) WL_X(FID_ffi_director_get_verdict) WL_X(FID_ffi_director_get_verdict_k154) WL_X(FID_ffi_director_get_verdict_k155) WL_X(FID_wire_get_list_go_6) WL_X(FID_wire_get_list_go_6_k157) WL_X(FID_wire_get_list_go_6_k158) WL_X(FID_director_decide_as) WL_X(FID_director_decide_as_k160) WL_X(FID_director_kept) WL_X(FID_director_kept_k162) WL_X(FID_wire_put_list_go_5) WL_X(FID_wire_put_list_go_5_k167) WL_X(FID_wire_put_list_go_2) WL_X(FID_wire_put_list_go_2_k172) WL_X(FID_wire_value) WL_X(FID_wire_value_k182) WL_X(FID_wire_get_list_7) WL_X(FID_wire_get_list_7_k185) WL_X(FID_wire_get_list_7_k186) WL_X(FID_child_env_merge) WL_X(FID_child_env_merge_k195) WL_X(FID_child_env_keep) WL_X(FID_child_env_keep_k197) WL_X(FID_child_env_keep_k198) WL_X(FID_wire_put_list_go_1) WL_X(FID_wire_put_list_go_1_k200) WL_X(FID_wire_put_list_go_1_k201) WL_X(FID_wire_get_list_5) WL_X(FID_wire_get_list_5_k204) WL_X(FID_wire_get_list_5_k205) WL_X(FID_director_decide) WL_X(FID_wire_put_list_5) WL_X(FID_wire_put_list_5_k217) WL_X(FID_List_length) WL_X(FID_List_length_k225) WL_X(FID_cvar_expand_go) WL_X(FID_cvar_expand_go_k227) WL_X(FID_ffi_cvar_get_alias) WL_X(FID_ffi_cvar_get_alias_k236) WL_X(FID_ffi_cvar_get_alias_k237) WL_X(FID_wire_get_list_go_3) WL_X(FID_wire_get_list_go_3_k239) WL_X(FID_wire_get_list_go_3_k240) WL_X(FID_wire_cdig_go) WL_X(FID_wire_cdig_go_k246) WL_X(FID_wire_get_nat_go) WL_X(FID_wire_get_nat_go_k249) WL_X(FID_wire_get_nat_go_k250) WL_X(FID_wire_get_nat_end) WL_X(FID_wire_get_nat_end_k252) WL_X(FID_wire_get_str) WL_X(FID_wire_get_str_k261) WL_X(FID_wire_get_list_go_1) WL_X(FID_wire_get_list_go_1_k263) WL_X(FID_wire_get_list_go_1_k264) WL_X(FID_wire_get_list_0) WL_X(FID_wire_get_list_0_k266) WL_X(FID_wire_get_list_0_k267) WL_X(FID_child_env_child) WL_X(FID_child_env_child_k271) WL_X(FID_wire_get_list_6) WL_X(FID_wire_get_list_6_k278) WL_X(FID_wire_get_list_6_k279) WL_X(FID_director_tick) WL_X(FID_director_tick_k282) WL_X(FID_director_tick_k283) WL_X(FID_director_tick_k284) WL_X(FID_director_tick_k285) WL_X(FID_ffi_cvar_get_bind) WL_X(FID_ffi_cvar_get_bind_k289) WL_X(FID_ffi_cvar_get_bind_k290) WL_X(FID_wire_get_list_go_4) WL_X(FID_wire_get_list_go_4_k292) WL_X(FID_wire_get_list_go_4_k293) WL_X(FID_U32_show_go) WL_X(FID_cvar_expand) WL_X(FID_cvar_expand_k297) WL_X(FID_cvar_expand_k298) WL_X(FID_ffi_cvar_put_cmds) WL_X(FID_ffi_cvar_put_cmds_k300) WL_X(FID_ffi_cvar_get_cmds) WL_X(FID_ffi_cvar_get_cmds_k306) WL_X(FID_ffi_cvar_get_cmds_k307) WL_X(FID_wire_tok) WL_X(FID_wire_tok_k312) WL_X(FID_ffi_director_get_loop) WL_X(FID_ffi_director_get_loop_k330) WL_X(FID_ffi_director_get_loop_k331) WL_X(FID_ffi_director_get_loop_k332) WL_X(FID_cvar_press) WL_X(FID_ffi_cvar_put_exp) WL_X(FID_ffi_cvar_put_exp_k345) WL_X(FID_Nat_show_fin) WL_X(FID_wire_get_list_3) WL_X(FID_wire_get_list_3_k349) WL_X(FID_wire_get_list_3_k350) WL_X(FID_wire_peek) WL_X(FID_wire_peek_k356) WL_X(FID_wire_get_u32) WL_X(FID_wire_get_u32_k361) WL_X(FID_wire_get_list_1) WL_X(FID_wire_get_list_1_k368) WL_X(FID_wire_get_list_1_k369) WL_X(FID_wire_get_list_4) WL_X(FID_wire_get_list_4_k384) WL_X(FID_wire_get_list_4_k385) WL_X(FID_U32_show) WL_X(FID_Nat_show) WL_X(FID_String_append) WL_X(FID_String_append_k396) WL_X(FID_ffi_cvar_get_xreq) WL_X(FID_ffi_cvar_get_xreq_k398) WL_X(FID_ffi_cvar_get_xreq_k399) WL_X(FID_wire_get_nat) WL_X(FID_wire_get_nat_k403) WL_X(FID_wire_get_nat_k404) WL_X(FID_ffi_child_env_get_req) WL_X(FID_ffi_child_env_get_req_k412) WL_X(FID_ffi_child_env_get_req_k413) WL_X(FID_ffi_child_env_get_req_k414) WL_X(FID_ffi_child_env_get_req_k415) WL_X(FID_ffi_director_get_req) WL_X(FID_ffi_director_get_req_k420) WL_X(FID_ffi_director_get_req_k421) WL_X(FID_ffi_director_get_req_k422) WL_X(FID_ffi_cvar_get_table) WL_X(FID_ffi_cvar_get_table_k427) WL_X(FID_ffi_cvar_get_table_k428) WL_X(FID_ffi_cvar_step) WL_X(FID_ffi_cvar_step_k433) WL_X(FID_ffi_cvar_step_k434) WL_X(FID_ffi_cvar_step_k435) WL_X(FID_ffi_echo_step) WL_X(FID_ffi_echo_step_k438) WL_X(FID_ffi_echo_step_k439) WL_X(FID_ffi_echo_step_k440) WL_X(FID_ffi_cvar_open) WL_X(FID_ffi_cvar_open_k462) WL_X(FID_ffi_echo_open) WL_X(FID_ffi_echo_open_k466) WL_X(FID_ffi_echo_open_k467) WL_X(FID_step_go) WL_X(FID_step_go_k470) WL_X(FID_step_go_k471) WL_X(FID_ffi_go) WL_X(FID_ffi_go_k474) WL_X(FID_ffi_go_k475) WL_X(FID_ffi_go_k476) WL_X(FID_ffi_go_k477) WL_X(FID_ffi_go_k478) WL_X(FID_ffi_go_k479) WL_X(FID_ffi_go_k480) WL_X(FID_ffi_go_k481) WL_X(FID_ffi_go_k482) WL_X(FID_ffi_go_k483) WL_X(FID_ffi_go_k484) WL_X(FID_ffi_go_k485) WL_X(FID_ffi_go_k486) WL_X(FID_ffi_go_k487) WL_X(FID_open_go) WL_X(FID_open_go_k491) WL_X(FID_open_go_k492) WL_X(FID_step) WL_X(FID_step_k494) WL_X(FID_close) WL_X(FID_ffi) WL_X(FID_ffi_k498) WL_X(FID_U32_read_go) WL_X(FID_open) WL_X(FID_open_k503) WL_X(FID_cli_steps) WL_X(FID_cli_steps_k505) WL_X(FID_cli_steps_k506) WL_X(FID_cli_steps_k507) WL_X(FID_U32_read) WL_X(FID_cli_print) WL_X(FID_cli_print_c519) WL_X(FID_cli_print_c520) WL_X(FID_cli_print_c521) WL_X(FID_cli_args) WL_X(FID_cli_args_k523) WL_X(FID_cli_args_k524) WL_X(FID_cli_args_k525) WL_X(FID_cli_args_k526) WL_X(FID_IO_bind) WL_X(FID_IO_bind_c530) WL_X(FID_IO_bind_k531) WL_X(FID_main) WL_X(FID_main_c533) WL_X(FID_main_c534) WL_X(FID_main_k535) WL_X(FID_main_c536) WL_X(FID_IO_args) WL_X(FID_IO_print) WL_X(FID_IO_emit) WL_X(FID_Clo_apply) WL_X(FID_EXIT)
#define MAIN_FID FID_main
#define MAIN_PURE 0
#define BLK_SHR 0

#define TAB_AT(T, S, I) T[S < I ? S : I]

#define fid_arity(x) FID_T[x].ar
#define fid_resw(x)  FID_T[x].resw
#define fid_bangs(x) FID_T[x].bangs
#define fid_nofk(x)  FID_T[x].nofk
#define cid_arity(x) CID_T[x].ar
#define cid_hot(x)   CID_T[x].hot

// A32
// ===

// C11's atomics on every lane; a device FENCE releases or acquires.
// Metal's loads read through a volatile local, or the M1 and M2 pipeline
// builds die. A weak CAS may fail with the cell still x: a32_cmpx loops.

#define A32_LOOP(k, x) \
  INLINE u32 a32_##k(DEV u32* p, u32 v) { \
    u32 o = a32_load(p); \
    while (!a32_cas(p, &o, x)) {} \
    return o; \
  }

#ifdef __METAL_VERSION__

INLINE DEV atomic_uint* A32(DEV u32* p) {
  return (DEV atomic_uint*)p;
}

INLINE TG atomic_uint* A32(TG u32* p) {
  return (TG atomic_uint*)p;
}

#define a32_load(p) \
  ({ volatile thread u32 _a32v = atomic_load_explicit(A32(p), RLX); _a32v; })

#else

#define a32_load(p) atomic_load_explicit(A32(p), RLX)

#ifdef BEND_RTC

#define A32(p) (p)
#define atomic_load_explicit(p, o)     (*(volatile u32*)(p))
#define atomic_store_explicit(p, v, o) (*(volatile u32*)(p) = (v))
#define atomic_fetch_add_explicit(p, v, o) atomicAdd((u32*)(p), v)
#define atomic_fetch_sub_explicit(p, v, o) atomicSub((u32*)(p), v)
#define atomic_fetch_and_explicit(p, v, o) atomicAnd((u32*)(p), v)
#define atomic_fetch_or_explicit(p, v, o) atomicOr((u32*)(p), v)
#define atomic_fetch_xor_explicit(p, v, o) atomicXor((u32*)(p), v)
#define atomic_fetch_min_explicit(p, v, o) atomicMin((u32*)(p), v)
#define atomic_fetch_max_explicit(p, v, o) atomicMax((u32*)(p), v)
#define atomic_compare_exchange_weak_explicit(p, e, v, s, f) a32_swp(p, e, v)

INLINE bool a32_swp(DEV u32* p, u32* e, u32 v) {
  u32 x = *e;
  *e = atomicCAS((u32*)p, x, v);
  return *e == x;
}

#else

#define A32(p) ((_Atomic u32*)(p))
#define atomic_fetch_min_explicit __c11_atomic_fetch_min
#define atomic_fetch_max_explicit __c11_atomic_fetch_max

#endif

#endif

#define RLX memory_order_relaxed

#if DEVICE
#define REL RLX
#define ACQ RLX
#define ACR RLX
#define a32_acq(p) FENCE()
#define w64_load(p) (*(p))
#else
#define REL memory_order_release
#define ACQ memory_order_acquire
#define ACR memory_order_acq_rel
#define a32_acq(p) ((void)a32_load_acq(p))
#define w64_load(p) atomic_load_explicit((_Atomic u64*)(p), RLX)
#endif

#define a32_store(p, v)     atomic_store_explicit(A32(p), v, RLX)
#define a32_add(p, v) atomic_fetch_add_explicit(A32(p), v, RLX)
#define a32_sub(p, v) atomic_fetch_sub_explicit(A32(p), v, RLX)
#define a32_and(p, v) atomic_fetch_and_explicit(A32(p), v, RLX)
#define a32_or(p, v) atomic_fetch_or_explicit(A32(p), v, RLX)
#define a32_xor(p, v) atomic_fetch_xor_explicit(A32(p), v, RLX)
#define a32_min(p, v) atomic_fetch_min_explicit(A32(p), v, RLX)
#define a32_max(p, v) atomic_fetch_max_explicit(A32(p), v, RLX)
#define a32_sub_rel(p, v)   (FENCE(), atomic_fetch_sub_explicit(A32(p), v, REL))
#define a32_store_rel(p, v) (FENCE(), atomic_store_explicit(A32(p), v, REL))
#define a32_at(H, word)     ((DEV u32*)&(H)[word])

INLINE u32 a32_load_acq(DEV u32* p) {
  u32 v = DEVICE ? a32_load(p) : atomic_load_explicit(A32(p), ACQ);
  FENCE();
  return v;
}

INLINE bool a32_cas(DEV u32* p, THR u32* e, u32 v) {
  FENCE();
  bool ok = atomic_compare_exchange_weak_explicit(A32(p), e, v, ACR, ACQ);
  FENCE();
  return ok;
}

A32_LOOP(exch, v)

INLINE u32 a32_cmpx(DEV u32* p, u32 x, u32 v) {
  u32 o = x;
  while (!a32_cas(p, &o, v) && o == x) {}
  return o;
}

// Err
// ===

#if DEVICE

INLINE void err_post(DEV u64* H, u32 code) {
  a32_cmpx(a32_at(H, H_ERROR_CODE), 0, code);
}

#else

static const char* ERR_TEXT[] = { "",
  "runtime fail-stop",
  "runtime fail-stop",
  "out of memory: run again with a bigger span, as in +RTS --gpu 8GB",
  "a function the device does not hold",
  "a Nat past the largest immediate 2^48-1",
  "runtime fail-stop",
  "memory fault (machine stack overflow?)",
  "an array past the deepest block class 31",
  "a value has more than 2^24-1 live copies: keep fewer alive at once, or build it again for some of them (each build counts its own copies)" };

// The first to fail gets 1; others wait a second for its _exit, then 0.
FAR int err_claim(void) {
  static _Atomic uintptr_t first;
  uintptr_t self = (uintptr_t)pthread_self(), seen = 0;
  if (atomic_compare_exchange_strong(&first, &seen, self)) return 1;
  struct timespec t = { seen != self, 0 };
  while (nanosleep(&t, &t)) {}
  return 0;
}

OUTLINE void err_fail(const char* msg) {
  if (err_claim()) fflush(stdout);
  fprintf(stderr, "bend: %s\n", msg);
  _exit(1);
}

static void err_post(u64* H, u32 code) {
  err_fail(ERR_TEXT[code]);
}

// A trap never waits on a lock: it flushes only if free, then writes raw.
static void err_trap(int sig) {
  static const char line[] = "bend: memory fault (machine stack overflow?)\n";
  if (err_claim() && ftrylockfile(stdout) == 0) fflush(stdout);
  if (write(2, line, sizeof line - 1)) {}
  _exit(1);
}

#endif

#define err_seen(H)    (DEVICE && a32_load(a32_at(H, H_ERROR_CODE)) != 0)
#define err_spun(H, n) ((++*(n) & 4095) == 0 && err_seen(H))

#if __METAL_VERSION__ >= 320
#define err_peek(H) *(volatile DEV u32*)a32_at(H, H_ERROR_CODE)
#else
#define err_peek err_seen
#endif

#ifdef __METAL_VERSION__
INLINE f32 atan2_c99(f32 y, f32 x) {
  return y == 0.0f && x == x
    ? copysign(signbit(x) ? M_PI_F : 0.0f, y) : atan2(y, x);
}
#define sqrt  precise::sqrt
#define exp   precise::exp
#define log   precise::log
#define log2  precise::log2
#define log10 precise::log10
#define sin   fast::sin
#define cos   fast::cos
#define tan   fast::tan
#define pow   precise::pow
#define fmod  precise::fmod
#define atan2 atan2_c99
#define U32_QUO(a, b) \
  ((a) / 2 / (b) * 2 + ((a) - (a) / 2 / (b) * 2 * (b) >= (b)))
#else
#define U32_QUO(a, b) ((a) / (b))
#endif

#define U32_BIN(a, o, b) ((u64)((u32)(a) o (u32)(b)))

INLINE u64 u32_pow(u32 a, u64 n) {
  u32 r = 1;
  for (; n; n >>= 1, a *= a) {
    if (n & 1) r *= a;
  }
  return r;
}

INLINE f32 f32_unbox(u64 x) {
  union { u32 u; f32 f; } p = { (u32)x };
  return p.f;
}

INLINE u64 f32_rewrap(f32 x) {
  union { f32 f; u32 u; } p = { x };
  return p.u;
}

INLINE u64 f32_to_u32(u64 a) {
  f32 v = f32_unbox(a);
  return v >= 0.0f && v < 4294967296.0f ? (u32)v : 0;
}

INLINE u64 nat_chk(Env e, u64 n) {
  if (n > NAT_IMM) {
    err_post(e.mem, ERR_NATS);
    return NAT_IMM;
  }
  return n;
}

INLINE u64 nat_mul(Env e, u64 a, u64 b) {
  return nat_chk(e, b != 0 && a > NAT_IMM / b ? NAT_IMM + 1 : a * b);
}

INLINE u64 map_msb_u(u64 n, u32 x) {
  if (n == 0 || x == 0) return 0;
  u64 width = 32 - CLZ(x);
  return n < width ? n : width;
}

#if DEVICE

#define f32_show(e, x) (err_post(e.mem, ERR_FIDS), 0)
#define f32_read(e, s) (err_post(e.mem, ERR_FIDS), 0)

#else

static Term f32_show(Env e, Term x);
static Term f32_read(Env e, Term s);

#endif

A32_LOOP(fadd, f32_rewrap(f32_unbox(o) + f32_unbox(v)))

// Bank
// ====

// A stack of exact generations per class. The host pops and pushes at rd;
// a device pass pops below rd and pushes above top, compacted after it.

#define bank_at(H, c) ((DEV Bank*)((H) + H_BANK) + (c))

INLINE u64 bank_pop(DEV u64* H, u32 c) {
  DEV Bank* b = bank_at(H, c);
  u64 got = 0;
  LOCK(bank_lock);
  u32 t = a32_sub(&b->rd, 1);
  if ((int)t > 0) {
    got = H[b->off + t - 1];
  } else {
    a32_add(&b->rd, 1);
  }
  if (!DEVICE) {
    b->wr = b->top = b->rd;
  }
  UNLOCK(bank_lock);
  return got;
}

INLINE void bank_push(DEV u64* H, u32 c, u64 head) {
  DEV Bank* b = bank_at(H, c);
  LOCK(bank_lock);
  H[b->off + a32_add(&b->wr, 1)] = head;
  if (!DEVICE) {
    b->rd = b->top = b->wr;
  }
  UNLOCK(bank_lock);
}

// Heap
// ====

// Per lane and class: a LIFO free chain, its length in words, and on the
// host COLD, one parked generation. A host free reaching KEEP_WORDS parks the
// chain as COLD and banks the old COLD. A miss takes COLD, a bank entry or a
// fresh quantum. A device lane banks its generations at the end (dev_cut).

#define ALC_AT(e, i)   (e).alc[(i) * LANE_STEP]
#define ALC_LEN(e, c)  ALC_AT(e, NCLS_ALL + (c))
#define ALC_COLD(e, c) ALC_AT(e, 2 * NCLS_ALL + (c))
#define KEEP(c)        (KEEP_WORDS >> (c) ? KEEP_WORDS >> (c) : 1)

INLINE u32 cls_fit(u32 words) {
  return words > 1 ? 32 - CLZ(words - 1) : 0;
}

OUTLINE void heap_hand(Env e, u32 cls) {
  u64 cold = ALC_COLD(e, cls);
  if (cold) {
    bank_push(e.mem, cls, cold);
  }
  ALC_COLD(e, cls) = ALC_AT(e, cls);
  ALC_AT(e, cls)   = ALC_LEN(e, cls) = 0;
}

#if DEVICE
#define corpus_grow(H, n) false
#else
static bool corpus_grow(u64* H, u64 need);
#endif

OUTLINE u64 heap_alloc_miss(Env e, u32 cls) {
  DEV u64* H = e.mem;
  u64  got = 0;
  if (!DEVICE) {
    got = ALC_COLD(e, cls);
    ALC_COLD(e, cls) = 0;
  }
  if (!got) {
    got = bank_pop(H, cls);
  }
  u32 n = got ? KEEP(cls) : cls < NCLS ? QUANTUM >> cls : 1;
  if (!got) {
    u32 pages = (n << cls) >> PAGE_BITS;
    u32 p     = a32_add(a32_at(H, H_BUMP), pages);
    if ((u64)p + pages > a32_load_acq(a32_at(H, H_CAP))
      && !corpus_grow(H, (u64)p + pages)) {
      err_post(H, ERR_HEAP);
      return HEAP_OFF;
    }
    got = HEAP_OFF + ((u64)p << PAGE_BITS);
    for (u32 i = 1; i <= n; i += 1) {
      H[got + ((u64)(i - 1) << cls)] = i < n ? got + ((u64)i << cls) : 0;
    }
  }
  ALC_AT(e, cls)  = H[got];
  ALC_LEN(e, cls) = (u64)(n - 1) << cls;
  return got;
}

INLINE u64 heap_alloc(Env e, u32 cls) {
  u64 h = ALC_AT(e, cls);
  if (h) {
    ALC_AT(e, cls)   = e.mem[h];
    ALC_LEN(e, cls) -= 1ull << cls;
    return h;
  }
  return heap_alloc_miss(e, cls);
}

INLINE void heap_free(Env e, u32 cls, u64 loc) {
  if (err_peek(e.mem)) {
    return;
  }
#ifdef BEND_POISON // a later read of a freed block fails
  for (u64 i = 1; i < 1ull << cls; i += 1) {
    e.mem[loc + i] = RFC_BIT | TAG_CTR << 56 | LOC_MASK;
  }
#endif
  e.mem[loc]       = ALC_AT(e, cls);
  ALC_AT(e, cls)   = loc;
  ALC_LEN(e, cls) += 1ull << cls;
  if (!DEVICE && ALC_LEN(e, cls) >= KEEP_WORDS) {
    heap_hand(e, cls);
  }
}

INLINE void spare_free(Env e, u32 cls, u64 loc) {
  if (loc >= HEAP_OFF) {
    heap_free(e, cls, loc);
  }
}

// Term
// ====

#define term_make(tag, aux, loc) \
  (((u64)(tag) << 56) | ((u64)(aux) << 40) | (u64)(loc))

#define term_ctr(cid, loc) term_make(TAG_CTR, cid, loc)
#define term_pak(cid, loc) term_make(TAG_PAK, cid, loc)
#define term_clo(fid, loc) term_make(TAG_CLO, fid, loc)
#define term_tsk(fid, loc) term_make(TAG_TSK, fid, loc)

INLINE Term term_blk(bool arr, u32 cls, u64 loc) {
  return term_make(arr ? TAG_ARR : TAG_BUF, cls, loc);
}

INLINE u64 term_tag(Term t) {
  return (t >> 56) & 0x7f;
}

INLINE bool term_rfc(Term t) {
  return (t & RFC_BIT) != 0;
}

INLINE u64 term_aux(Term t) {
  return (t >> 40) & 0xFFFF;
}

INLINE u64 term_loc(Term t) {
  return t & LOC_MASK;
}

INLINE bool term_triv(Term t) {
  return term_tag(t) <= TAG_PAK || t == TERM_HOLE || term_loc(t) < HEAP_OFF;
}

OUTLINE Term rfc_wrap(Env e, Term t, u32 cnt) {
  if (term_tag(t) == TAG_CLO || term_tag(t) == TAG_TSK) {
    err_post(e.mem, ERR_RFCS);
    return t;
  }
  u64 r = heap_alloc(e, 0);
  e.mem[r] = (term_loc(t) << 24) | cnt;
  return (t & ~LOC_MASK) | RFC_BIT | r;
}

INLINE Term rfc_seal(Env e, Term t) {
  if (term_tag(t) != TAG_CTR || term_rfc(t)) {
    return t;
  }
  return rfc_wrap(e, t, 1);
}

INLINE void rfc_bump(Env e, u64 r, u32 k) {
  u32 c = a32_add(a32_at(e.mem, r), k);
  if ((c & RFC_CNT) >= RFC_CNT - k) {
    err_post(e.mem, ERR_CNTS);
  }
}

INLINE Term term_keep(Env e, Term t, u32 k) {
  if (term_rfc(t)) {
    rfc_bump(e, term_loc(t), k);
    return t;
  }
  if (term_triv(t)) {
    return t;
  }
  return rfc_wrap(e, t, 1 + k);
}

// A redirect cell holds its target's loc over a 24-bit count, which only
// atomic adds on the low word change: the loc bits never do. The host reads
// the cell in one relaxed 64-bit load; the device's plain load may tear into
// two halves, both holding the same loc. A shared node's fields never change
// either, so ctr_take copies them before it acquires.
INLINE u64 term_peek(DEV u64* H, Term t) {
  if (term_rfc(t)) {
    return w64_load(&H[term_loc(t)]) >> 24;
  }
  return term_loc(t);
}

// Base's Map.bit, reading the key in place: 33 bits a char, a presence bit
// then the code MSB first, false past the end
INLINE u64 map_bit(Env e, Term key, u64 pos) {
  for (u64 i = pos / 33; i > 0 && term_aux(key) == CID_SCon; i -= 1) {
    key = e.mem[term_peek(e.mem, key) + 1];
  }
  if (term_aux(key) != CID_SCon) return 0;
  u64 off = pos % 33;
  return off == 0 || (((u32)e.mem[term_peek(e.mem, key)] >> (32 - off)) & 1);
}

#define blk_shr(t) (BLK_SHR && term_rfc(t))

#define blk_loc(H, a) (BLK_SHR ? term_peek(H, a) : term_loc(a))

INLINE u32 blk_cls(Term t) {
  return (u32)term_aux(t) & 31;
}

INLINE u32 blk_wcls(bool arr, u32 c) {
  return arr ? c : c == 0 ? 0 : c - 1;
}

INLINE u32 blk_span(Term t) {
  return blk_wcls(term_tag(t) == TAG_ARR, blk_cls(t));
}

// A node's first word holds its frame, freed before its last live child; a
// spine field swaps to the end, so a list drops cell by cell. A live end
// under 256 fits the frame, a wider one the (trivial) last cell.
FAR void term_drop(Env e, Term t) {
  DEV u64* H = e.mem;
  u64  cur = 0;
  Term c0  = 0;
  u32  step = 0;
  for (;;) {
    if (!term_triv(t) && term_rfc(t)) {
      u64      r = term_loc(t);
      DEV u32* p = a32_at(H, r);
      if ((a32_sub_rel(p, 1) & RFC_CNT) != 1) {
        t = 0;
      } else {
        a32_acq(p);
        t = (t & ~(RFC_BIT | LOC_MASK)) | (H[r] >> 24);
        heap_free(e, 0, r);
      }
    }
    if (!term_triv(t)) {
      u64 tag = term_tag(t);
      if (tag == TAG_BUF) {
        heap_free(e, blk_span(t), term_loc(t));
      } else {
        u32 aux = (u32)term_aux(t);
        u64 loc = term_loc(t);
        u32 n = tag == TAG_ARR ? 0 : tag == TAG_CTR ? cid_arity(aux)
          : fid_arity(aux) - (tag == TAG_CLO),
          cls = tag == TAG_ARR ? 64 | blk_cls(t)
          : n > 247 ? 64 | (n - 240)
          : cls_fit(tag == TAG_TSK ? n + 2 : n),
          w = cls < 64 ? n : 1u << (cls & 63),
          d = tag == TAG_CTR ? CID_T[aux].spine : 0, m = w;
        if (d) {
          u64 end = loc + w - 1;
          Term f = H[end - d];
          H[end - d] = H[end];
          H[end] = f;
        }
        while (m && term_triv(H[loc + m - 1])) --m;
        if (m < 256) {
          n   = m;
          cls &= 63;
        } else if (m < w) {
          H[loc + w - 1] = m;
        }
        c0 = m ? H[loc] : 0;
        H[loc] = cur;
        cur = loc | ((u64)n << 48) | ((u64)cls << 56);
      }
    }
    for (;;) {
      if (err_spun(H, &step) || cur == 0) {
        return;
      }
      u64  loc = cur & LOC_MASK;
      u32  i   = (u8)(cur >> 40);
      u32  n   = (u8)(cur >> 48);
      u32  cls = (u32)(cur >> 56);
      bool arr = cls > 63;
      u32  j   = i;
      if (arr) {
        cls &= 63;
        n   = 1u << cls;
        Term z = H[loc + (i > 1 ? 1 : n - 1)];
        n = i > 1 ? z >> 32 : term_triv(z) ? (u32)z : n;
        j = i > 1 ? (u32)z : i;
      }
      Term c = j == 0 ? c0 : H[loc + j];
      if (j + 1 >= n) {
        cur = H[loc];
        heap_free(e, cls, loc);
      } else {
        if (arr && j) {
          H[loc + 1] = (u64)n << 32 | (j + 1);
        }
        if (!arr || i < 2) {
          cur += 1ull << 40;
        }
      }
      if (!term_triv(c)) {
        t = c;
        break;
      }
    }
  }
}

INLINE void term_sink(Env e, Term t) {
  if (!term_triv(t)) {
    term_drop(e, t);
  }
}

OUTLINE void span_fade(Env e, Term t, u64 src, u32 n) {
  for (u32 j = 0; j < n; j += 1) {
    Term f = e.mem[src + j];
    if (term_rfc(f)) {
      rfc_bump(e, term_loc(f), 1);
    } else if (!term_triv(f)) {
      err_post(e.mem, ERR_RFCS);
    }
  }
  term_drop(e, t);
}

INLINE u64 ctr_take(Env e, Term t, u32 n, THR Term* out) {
  DEV u64* H = e.mem;
  u64 src = term_peek(H, t);
  for (u32 j = 0; j < n; j += 1) {
    out[j] = H[src + j];
  }
  if (!term_rfc(t)) {
    return src;
  }
  DEV u32* c = a32_at(H, term_loc(t));
  if ((a32_load(c) & RFC_CNT) == 1) {
    a32_acq(c);
    heap_free(e, 0, term_loc(t));
    return src;
  }
  span_fade(e, t, src, n);
  return 0;
}

INLINE Term term_word(Env e, Term w) {
  u32 x = 0;
  Term t = w;
  for (u32 i = 0; i < 32 && term_aux(t) == CID_WCon; i += 1) {
    u64 l = term_peek(e.mem, t);
    x |= (u32)(e.mem[l] & 1) << i;
    t = e.mem[l + 1];
  }
  term_sink(e, w);
  return x;
}

// Blk
// ===

// A block owns one allocation in its class (an ARR 2^c Terms, a BUF 2^c
// u32). Matching ANode is blk_half twice (the high call frees the source).

#define BLK_ALLOC(n, w) \
  u64 n = heap_alloc(e, w); \
  if (err_seen(e.mem)) { \
    return term_blk(0, 0, n); \
  }

INLINE DEV u32a* blk_ptr(DEV u64* H, u64 loc, u32 i) {
  return (DEV u32a*)(H + loc) + i;
}

INLINE Term blk_read(DEV u64* H, bool arr, u64 loc, u32 i) {
  if (arr) {
    return H[loc + i];
  }
  return (u64)*blk_ptr(H, loc, i);
}

INLINE void blk_write(DEV u64* H, bool arr, u64 loc, u32 i, Term v) {
  if (arr) {
    H[loc + i] = v;
  } else {
    *blk_ptr(H, loc, i) = (u32)v;
  }
}

INLINE u32 blk_at(Term a, u64 i, u32 lgs) {
  return ((u32)i & (u32)((1ull << (blk_cls(a) - lgs)) - 1)) << lgs;
}

INLINE Term blk_keep(Env e, u64 at) {
  Term w = e.mem[at];
  Term v = term_keep(e, w, 1);
  if (v != w) {
    e.mem[at] = v;
  }
  return v;
}

INLINE void blk_fill(Env e, u64 dst, u64 src, u64 n, bool keep) {
  for (u64 j = 0; j < n; j += 1) {
    e.mem[dst + j] = keep ? blk_keep(e, src + j) : e.mem[src + j];
  }
}

INLINE void blk_free(Env e, Term t) {
  blk_shr(t) ? term_drop(e, t) : heap_free(e, blk_span(t), term_loc(t));
}

OUTLINE Term blk_copy(Env e, Term a) {
  bool arr = term_tag(a) == TAG_ARR;
  u32 cls = blk_span(a);
  BLK_ALLOC(dst, cls)
  blk_fill(e, dst, blk_loc(e.mem, a), 1ull << cls, arr);
  return term_blk(arr, blk_cls(a), dst);
}

INLINE Term blk_node(Env e, Term l, Term r) {
  DEV u64* H = e.mem;
  bool arr = term_tag(l) == TAG_ARR;
  u32 c = blk_cls(l);
  if (c != blk_cls(r) || c + 1 >= NCLS_ALL) {
    err_post(H, ERR_TAGS);
    return l;
  }
  u64 pl = blk_loc(H, l);
  u64 pr = blk_loc(H, r);
  BLK_ALLOC(n, arr ? c + 1 : c)
  if (!arr && c == 0) {
    H[n] = (u64)*blk_ptr(H, pl, 0) | ((u64)*blk_ptr(H, pr, 0) << 32);
  } else {
    u64 cw = 1ull << blk_span(l);
    blk_fill(e, n, pl, cw, arr && blk_shr(l));
    blk_fill(e, n + cw, pr, cw, arr && blk_shr(r));
  }
  blk_free(e, l);
  blk_free(e, r);
  return term_blk(arr, c + 1, n);
}

INLINE Term blk_half(Env e, Term a, u32 hi) {
  DEV u64* H = e.mem;
  bool arr = term_tag(a) == TAG_ARR;
  u32 c = blk_cls(a);
  if (c == 0) {
    err_post(H, ERR_TAGS);
    return a;
  }
  c -= 1;
  u32 cw = blk_wcls(arr, c);
  u64 src = blk_loc(H, a);
  BLK_ALLOC(n, cw)
  if (!arr && c == 0) {
    H[n] = (u64)*blk_ptr(H, src, hi);
  } else {
    blk_fill(e, n, src + ((u64)hi << cw), 1ull << cw, arr && blk_shr(a));
  }
  if (hi) {
    blk_free(e, a);
  }
  return term_blk(arr, c, n);
}

INLINE Term blk_new(Env e, bool arr, u64 d, u32 lgs, u32 n, THR Term* v) {
  DEV u64* H = e.mem;
  if (d + lgs > 31) {
    err_post(H, ERR_ARRS);
    d = 0;
  }
  u32 c = (u32)d + lgs;
  BLK_ALLOC(l, blk_wcls(arr, c))
  for (u32 j = 0; arr && d > 0 && j < n; j += 1) {
    if (d >= 24 && !term_triv(v[j])) {
      err_post(H, ERR_CNTS);
    }
    v[j] = term_keep(e, v[j], (1u << d) - 1);
  }
  for (u64 i = 0; i < (1ull << c); i += 1) {
    blk_write(H, arr, l, (u32)i, i % (1u << lgs) < n ? v[i % (1u << lgs)] : 0);
  }
  return term_blk(arr, c, l);
}

// Ring
// ====

#define ring_word(H, r, w) ((H) + RING_OFF + (w) * LANES + (r))
#define ring_slot(H, r, p) ring_word(H, r, (p) & (RING_LEN - 1))
#define ring_get(H, r)     ((DEV u32*)ring_word(H, r, RING_LEN))
#define ring_put(H, r)     ((DEV u32*)ring_word(H, r, RING_LEN + 1))
#define ring_held(H, r)    (ring_put(H, r) + 1)

INLINE u32 ring_lap(u32 pos) {
  return ~(u32)(pos / RING_LEN) & 1;
}

INLINE void ring_push(DEV u64* H, u32 r, Term tsk) {
  u32 pos = a32_add(ring_put(H, r), 1);
  if (pos - a32_load(ring_get(H, r)) >= RING_LEN) {
    err_post(H, ERR_RING);
    return;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, r, pos);
  a32_store(lo, (u32)tsk);
  a32_store_rel(lo + 1, (u32)(tsk >> 32) | (ring_lap(pos) << 31));
}

INLINE u32 ring_flip(u32 i) {
  return (i % CUBE_T << CUBE_LOG) + i / CUBE_T;
}

// A turn's five dispatches (x, y, z) sit at H_GROUPS, before H_ROOT_DONE.
typedef char turn_fits[H_GROUPS + 8 <= H_ROOT_DONE ? 1 : -1];

#define TURN_ROWS(at) ((at) % 4 == 0 ? 1 : CUBE_G)

INLINE u32 turn_groups(u64 f, u32 at) {
  bool run = f != 0 && (at == 2 ? f >= CUBE_T : at == 1 ? f < LANES
    : at == 4 || f < CUBE_T);
  return run ? TURN_ROWS(at) : 0;
}

INLINE void turn_set(DEV u64* H, u64 f) {
  DEV u32* g = (DEV u32*)(H + H_GROUPS);
  H[H_FRONT] = f;
  for (u32 i = 0; i < 15; i += 1) {
    g[i] = i % 3 != 0 ? 1 : turn_groups(f, i / 3);
  }
}

#define ring_pick(b, s, c) ((b) + (s) * (a32_add(c, 1) & (CUBE_T - 1)))

// Task
// ====

INLINE u64 task_node(Env e, u32 fid, Term cont, u32 idx, u32 rem) {
  u32 ar  = fid_arity(fid);
  u64 loc = heap_alloc(e, cls_fit(ar + 2));
  for (u32 i = 0; rem && i < ar; i += 1) {
    e.mem[loc + i] = TERM_HOLE;
  }
  e.mem[loc + ar]     = cont;
  e.mem[loc + ar + 1] = ((u64)idx << 32) | rem;
  return loc;
}

INLINE u64 task_tail(Term t) {
  return term_loc(t) + fid_arity((u32)term_aux(t));
}

INLINE Term task_deliver(DEV u64* H, Term cont, u32 idx, THR Term* v, u32 n) {
  u64 at = cont == TERM_HOLE ? H_ROOT_WORD : term_loc(cont) + idx;
  for (u32 j = 0; j < WL_RESW; j += 1) {
    if (j < n) {
      H[at + j] = v[j];
    }
  }
  if (cont == TERM_HOLE) {
    a32_store_rel(a32_at(H, H_ROOT_DONE), n + 1);
    return 0;
  }
  DEV u32* c = a32_at(H, task_tail(cont) + 1);
  if (a32_sub_rel(c, 1) == 1) {
    a32_acq(c);
    return cont;
  }
  return 0;
}

INLINE void task_deal(DEV u64* H, Term join, u32 base, u32 stride, TG u32* cur) {
  u64 loc = term_loc(join);
  u32 ar  = fid_arity((u32)term_aux(join));
  u32 g   = 0;
  if (stride == 0) {
    g = a32_add(a32_at(H, H_CURSOR), (u32)H[loc + ar + 1]);
  }
  for (u32 i = 0; i < ar; i += 1) {
    Term k = H[loc + i];
    if (term_tag(k) == TAG_TSK) {
      H[loc + i] = TERM_HOLE;
      ring_push(H, stride != 0 ? ring_pick(base, stride, cur)
        : ring_flip(g & (u32)(LANES - 1)), k);
      g += 1;
    }
  }
}

// Root
// ====

INLINE bool root_done(DEV u64* H) {
  return a32_load_acq(a32_at(H, H_ROOT_DONE)) != 0;
}

static u32 root_take(DEV u64* H, THR Term* v) {
  u32 n = a32_load_acq(a32_at(H, H_ROOT_DONE)) - 1;
  for (u32 j = 0; j < n; j += 1) {
    v[j] = H[H_ROOT_WORD + j];
  }
  a32_store(a32_at(H, H_ROOT_DONE), 0);
  return n;
}

// Spins
// =====

CONSTV u64 STAT_IMG[] = { 89ull, term_pak(CID_SNil, 0), 69ull, term_ctr(CID_SCon, STAT_OFF + 0), 75ull, term_ctr(CID_SCon, STAT_OFF + 2), 95ull, term_ctr(CID_SCon, STAT_OFF + 4), 73ull, term_ctr(CID_SCon, STAT_OFF + 6), 80ull, term_ctr(CID_SCon, STAT_OFF + 8), 65ull, term_ctr(CID_SCon, STAT_OFF + 10), 73ull, term_ctr(CID_SCon, STAT_OFF + 4), 80ull, term_ctr(CID_SCon, STAT_OFF + 14), 65ull, term_ctr(CID_SCon, STAT_OFF + 16), 78ull, term_pak(CID_SNil, 0), 69ull, term_ctr(CID_SCon, STAT_OFF + 20), 75ull, term_ctr(CID_SCon, STAT_OFF + 22), 79ull, term_ctr(CID_SCon, STAT_OFF + 24), 84ull, term_ctr(CID_SCon, STAT_OFF + 26), 84ull, term_pak(CID_SNil, 0), 69ull, term_ctr(CID_SCon, STAT_OFF + 30), 82ull, term_ctr(CID_SCon, STAT_OFF + 32), 67ull, term_ctr(CID_SCon, STAT_OFF + 34), 69ull, term_ctr(CID_SCon, STAT_OFF + 36), 83ull, term_ctr(CID_SCon, STAT_OFF + 38), 68ull, term_pak(CID_SNil, 0), 82ull, term_ctr(CID_SCon, STAT_OFF + 42), 79ull, term_ctr(CID_SCon, STAT_OFF + 44), 87ull, term_ctr(CID_SCon, STAT_OFF + 46), 83ull, term_ctr(CID_SCon, STAT_OFF + 48), 83ull, term_ctr(CID_SCon, STAT_OFF + 50), 65ull, term_ctr(CID_SCon, STAT_OFF + 52), 80ull, term_ctr(CID_SCon, STAT_OFF + 54), 87ull, term_ctr(CID_SCon, STAT_OFF + 42), 83ull, term_ctr(CID_SCon, STAT_OFF + 58), 83ull, term_ctr(CID_SCon, STAT_OFF + 60), 65ull, term_ctr(CID_SCon, STAT_OFF + 62), 80ull, term_ctr(CID_SCon, STAT_OFF + 64), 69ull, term_pak(CID_SNil, 0), 83ull, term_ctr(CID_SCon, STAT_OFF + 68), 65ull, term_ctr(CID_SCon, STAT_OFF + 70), 82ull, term_ctr(CID_SCon, STAT_OFF + 72), 72ull, term_ctr(CID_SCon, STAT_OFF + 74), 80ull, term_ctr(CID_SCon, STAT_OFF + 76), 83ull, term_ctr(CID_SCon, STAT_OFF + 78), 83ull, term_ctr(CID_SCon, STAT_OFF + 80), 65ull, term_ctr(CID_SCon, STAT_OFF + 82), 80ull, term_ctr(CID_SCon, STAT_OFF + 84), 76ull, term_pak(CID_SNil, 0), 65ull, term_ctr(CID_SCon, STAT_OFF + 88), 73ull, term_ctr(CID_SCon, STAT_OFF + 90), 84ull, term_ctr(CID_SCon, STAT_OFF + 92), 78ull, term_ctr(CID_SCon, STAT_OFF + 94), 69ull, term_ctr(CID_SCon, STAT_OFF + 96), 68ull, term_ctr(CID_SCon, STAT_OFF + 98), 69ull, term_ctr(CID_SCon, STAT_OFF + 100), 82ull, term_ctr(CID_SCon, STAT_OFF + 102), 67ull, term_ctr(CID_SCon, STAT_OFF + 104), 69ull, term_ctr(CID_SCon, STAT_OFF + 6), 84ull, term_ctr(CID_SCon, STAT_OFF + 108), 65ull, term_ctr(CID_SCon, STAT_OFF + 110), 86ull, term_ctr(CID_SCon, STAT_OFF + 112), 73ull, term_ctr(CID_SCon, STAT_OFF + 114), 82ull, term_ctr(CID_SCon, STAT_OFF + 116), 80ull, term_ctr(CID_SCon, STAT_OFF + 118), 83ull, term_ctr(CID_SCon, STAT_OFF + 6), 83ull, term_ctr(CID_SCon, STAT_OFF + 122), 69ull, term_ctr(CID_SCon, STAT_OFF + 124), 67ull, term_ctr(CID_SCon, STAT_OFF + 126), 67ull, term_ctr(CID_SCon, STAT_OFF + 128), 65ull, term_ctr(CID_SCon, STAT_OFF + 130), term_ctr(CID_SCon, STAT_OFF + 132), term_pak(CID_Nil, 0), term_ctr(CID_SCon, STAT_OFF + 120), term_ctr(CID_Con, STAT_OFF + 134), term_ctr(CID_SCon, STAT_OFF + 106), term_ctr(CID_Con, STAT_OFF + 136), term_ctr(CID_SCon, STAT_OFF + 86), term_ctr(CID_Con, STAT_OFF + 138), term_ctr(CID_SCon, STAT_OFF + 66), term_ctr(CID_Con, STAT_OFF + 140), term_ctr(CID_SCon, STAT_OFF + 56), term_ctr(CID_Con, STAT_OFF + 142), term_ctr(CID_SCon, STAT_OFF + 40), term_ctr(CID_Con, STAT_OFF + 144), term_ctr(CID_SCon, STAT_OFF + 28), term_ctr(CID_Con, STAT_OFF + 146), term_ctr(CID_SCon, STAT_OFF + 18), term_ctr(CID_Con, STAT_OFF + 148), term_ctr(CID_SCon, STAT_OFF + 12), term_ctr(CID_Con, STAT_OFF + 150), 116ull, term_pak(CID_SNil, 0), 115ull, term_ctr(CID_SCon, STAT_OFF + 154), 101ull, term_ctr(CID_SCon, STAT_OFF + 156), 117ull, term_ctr(CID_SCon, STAT_OFF + 158), 113ull, term_ctr(CID_SCon, STAT_OFF + 160), 101ull, term_ctr(CID_SCon, STAT_OFF + 162), 114ull, term_ctr(CID_SCon, STAT_OFF + 164), 32ull, term_ctr(CID_SCon, STAT_OFF + 166), 101ull, term_ctr(CID_SCon, STAT_OFF + 168), 114ull, term_ctr(CID_SCon, STAT_OFF + 170), 105ull, term_ctr(CID_SCon, STAT_OFF + 172), 119ull, term_ctr(CID_SCon, STAT_OFF + 174), 32ull, term_ctr(CID_SCon, STAT_OFF + 176), 100ull, term_ctr(CID_SCon, STAT_OFF + 178), 101ull, term_ctr(CID_SCon, STAT_OFF + 180), 109ull, term_ctr(CID_SCon, STAT_OFF + 182), 114ull, term_ctr(CID_SCon, STAT_OFF + 184), 111ull, term_ctr(CID_SCon, STAT_OFF + 186), 102ull, term_ctr(CID_SCon, STAT_OFF + 188), 108ull, term_ctr(CID_SCon, STAT_OFF + 190), 97ull, term_ctr(CID_SCon, STAT_OFF + 192), 109ull, term_ctr(CID_SCon, STAT_OFF + 194), 57ull, term_pak(CID_Nil, 0), 56ull, term_ctr(CID_Con, STAT_OFF + 198), 55ull, term_ctr(CID_Con, STAT_OFF + 200), 54ull, term_ctr(CID_Con, STAT_OFF + 202), 53ull, term_ctr(CID_Con, STAT_OFF + 204), 52ull, term_ctr(CID_Con, STAT_OFF + 206), 51ull, term_ctr(CID_Con, STAT_OFF + 208), 50ull, term_ctr(CID_Con, STAT_OFF + 210), 49ull, term_ctr(CID_Con, STAT_OFF + 212), 48ull, term_ctr(CID_Con, STAT_OFF + 214), 0, term_pak(CID_Nil, 0), 48ull, term_pak(CID_SNil, 0), 114ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 222), 118ull, term_ctr(CID_SCon, STAT_OFF + 224), 111ull, term_ctr(CID_SCon, STAT_OFF + 226), 32ull, term_ctr(CID_SCon, STAT_OFF + 228), 116ull, term_ctr(CID_SCon, STAT_OFF + 230), 102ull, term_ctr(CID_SCon, STAT_OFF + 232), 101ull, term_ctr(CID_SCon, STAT_OFF + 234), 108ull, term_ctr(CID_SCon, STAT_OFF + 236), 32ull, term_ctr(CID_SCon, STAT_OFF + 238), 116ull, term_ctr(CID_SCon, STAT_OFF + 240), 117ull, term_ctr(CID_SCon, STAT_OFF + 242), 112ull, term_ctr(CID_SCon, STAT_OFF + 244), 110ull, term_ctr(CID_SCon, STAT_OFF + 246), 105ull, term_ctr(CID_SCon, STAT_OFF + 248), 32ull, term_ctr(CID_SCon, STAT_OFF + 250), 58ull, term_ctr(CID_SCon, STAT_OFF + 252), 114ull, term_ctr(CID_SCon, STAT_OFF + 254), 97ull, term_ctr(CID_SCon, STAT_OFF + 256), 118ull, term_ctr(CID_SCon, STAT_OFF + 258), 99ull, term_ctr(CID_SCon, STAT_OFF + 260), 118ull, term_ctr(CID_SCon, STAT_OFF + 254), 110ull, term_ctr(CID_SCon, STAT_OFF + 264), 101ull, term_ctr(CID_SCon, STAT_OFF + 266), 95ull, term_ctr(CID_SCon, STAT_OFF + 268), 100ull, term_ctr(CID_SCon, STAT_OFF + 270), 108ull, term_ctr(CID_SCon, STAT_OFF + 272), 105ull, term_ctr(CID_SCon, STAT_OFF + 274), 104ull, term_ctr(CID_SCon, STAT_OFF + 276), 99ull, term_ctr(CID_SCon, STAT_OFF + 278), 111ull, term_ctr(CID_SCon, STAT_OFF + 256), 116ull, term_ctr(CID_SCon, STAT_OFF + 282), 99ull, term_ctr(CID_SCon, STAT_OFF + 284), 101ull, term_ctr(CID_SCon, STAT_OFF + 286), 114ull, term_ctr(CID_SCon, STAT_OFF + 288), 105ull, term_ctr(CID_SCon, STAT_OFF + 290), 100ull, term_ctr(CID_SCon, STAT_OFF + 292), 32ull, term_ctr(CID_SCon, STAT_OFF + 262), 69ull, term_ctr(CID_SCon, STAT_OFF + 296), 121ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 300), 107ull, term_ctr(CID_SCon, STAT_OFF + 302), 32ull, term_ctr(CID_SCon, STAT_OFF + 304), 100ull, term_ctr(CID_SCon, STAT_OFF + 306), 101ull, term_ctr(CID_SCon, STAT_OFF + 308), 109ull, term_ctr(CID_SCon, STAT_OFF + 310), 114ull, term_ctr(CID_SCon, STAT_OFF + 312), 111ull, term_ctr(CID_SCon, STAT_OFF + 314), 102ull, term_ctr(CID_SCon, STAT_OFF + 316), 108ull, term_ctr(CID_SCon, STAT_OFF + 318), 97ull, term_ctr(CID_SCon, STAT_OFF + 320), 109ull, term_ctr(CID_SCon, STAT_OFF + 322), 32ull, term_ctr(CID_SCon, STAT_OFF + 324), 58ull, term_ctr(CID_SCon, STAT_OFF + 326), 114ull, term_ctr(CID_SCon, STAT_OFF + 328), 97ull, term_ctr(CID_SCon, STAT_OFF + 330), 118ull, term_ctr(CID_SCon, STAT_OFF + 332), 99ull, term_ctr(CID_SCon, STAT_OFF + 334), 32ull, term_ctr(CID_SCon, STAT_OFF + 336), 69ull, term_ctr(CID_SCon, STAT_OFF + 338), 100ull, term_ctr(CID_SCon, STAT_OFF + 168), 110ull, term_ctr(CID_SCon, STAT_OFF + 342), 97ull, term_ctr(CID_SCon, STAT_OFF + 344), 112ull, term_ctr(CID_SCon, STAT_OFF + 346), 120ull, term_ctr(CID_SCon, STAT_OFF + 348), 101ull, term_ctr(CID_SCon, STAT_OFF + 350), 32ull, term_ctr(CID_SCon, STAT_OFF + 352), 100ull, term_ctr(CID_SCon, STAT_OFF + 354), 101ull, term_ctr(CID_SCon, STAT_OFF + 356), 109ull, term_ctr(CID_SCon, STAT_OFF + 358), 114ull, term_ctr(CID_SCon, STAT_OFF + 360), 111ull, term_ctr(CID_SCon, STAT_OFF + 362), 102ull, term_ctr(CID_SCon, STAT_OFF + 364), 108ull, term_ctr(CID_SCon, STAT_OFF + 366), 97ull, term_ctr(CID_SCon, STAT_OFF + 368), 109ull, term_ctr(CID_SCon, STAT_OFF + 370), 32ull, term_ctr(CID_SCon, STAT_OFF + 372), 58ull, term_ctr(CID_SCon, STAT_OFF + 374), 114ull, term_ctr(CID_SCon, STAT_OFF + 376), 97ull, term_ctr(CID_SCon, STAT_OFF + 378), 118ull, term_ctr(CID_SCon, STAT_OFF + 380), 99ull, term_ctr(CID_SCon, STAT_OFF + 382), 101ull, term_ctr(CID_SCon, STAT_OFF + 342), 109ull, term_ctr(CID_SCon, STAT_OFF + 386), 114ull, term_ctr(CID_SCon, STAT_OFF + 388), 111ull, term_ctr(CID_SCon, STAT_OFF + 390), 102ull, term_ctr(CID_SCon, STAT_OFF + 392), 108ull, term_ctr(CID_SCon, STAT_OFF + 394), 97ull, term_ctr(CID_SCon, STAT_OFF + 396), 109ull, term_ctr(CID_SCon, STAT_OFF + 398), 32ull, term_ctr(CID_SCon, STAT_OFF + 400), 58ull, term_ctr(CID_SCon, STAT_OFF + 402), 118ull, term_ctr(CID_SCon, STAT_OFF + 404), 110ull, term_ctr(CID_SCon, STAT_OFF + 406), 101ull, term_ctr(CID_SCon, STAT_OFF + 408), 95ull, term_ctr(CID_SCon, STAT_OFF + 410), 100ull, term_ctr(CID_SCon, STAT_OFF + 412), 108ull, term_ctr(CID_SCon, STAT_OFF + 414), 105ull, term_ctr(CID_SCon, STAT_OFF + 416), 104ull, term_ctr(CID_SCon, STAT_OFF + 418), 99ull, term_ctr(CID_SCon, STAT_OFF + 420), 114ull, term_ctr(CID_SCon, STAT_OFF + 404), 111ull, term_ctr(CID_SCon, STAT_OFF + 424), 116ull, term_ctr(CID_SCon, STAT_OFF + 426), 99ull, term_ctr(CID_SCon, STAT_OFF + 428), 101ull, term_ctr(CID_SCon, STAT_OFF + 430), 114ull, term_ctr(CID_SCon, STAT_OFF + 432), 105ull, term_ctr(CID_SCon, STAT_OFF + 434), 100ull, term_ctr(CID_SCon, STAT_OFF + 436), 101ull, term_pak(CID_SNil, 0), 108ull, term_ctr(CID_SCon, STAT_OFF + 440), 98ull, term_ctr(CID_SCon, STAT_OFF + 442), 97ull, term_ctr(CID_SCon, STAT_OFF + 444), 116ull, term_ctr(CID_SCon, STAT_OFF + 446), 32ull, term_ctr(CID_SCon, STAT_OFF + 448), 115ull, term_ctr(CID_SCon, STAT_OFF + 450), 115ull, term_ctr(CID_SCon, STAT_OFF + 452), 101ull, term_ctr(CID_SCon, STAT_OFF + 454), 114ull, term_ctr(CID_SCon, STAT_OFF + 456), 112ull, term_ctr(CID_SCon, STAT_OFF + 458), 32ull, term_ctr(CID_SCon, STAT_OFF + 460), 100ull, term_ctr(CID_SCon, STAT_OFF + 462), 101ull, term_ctr(CID_SCon, STAT_OFF + 464), 109ull, term_ctr(CID_SCon, STAT_OFF + 466), 114ull, term_ctr(CID_SCon, STAT_OFF + 468), 111ull, term_ctr(CID_SCon, STAT_OFF + 470), 102ull, term_ctr(CID_SCon, STAT_OFF + 472), 108ull, term_ctr(CID_SCon, STAT_OFF + 474), 97ull, term_ctr(CID_SCon, STAT_OFF + 476), 109ull, term_ctr(CID_SCon, STAT_OFF + 478), 32ull, term_ctr(CID_SCon, STAT_OFF + 480), 58ull, term_ctr(CID_SCon, STAT_OFF + 482), 114ull, term_ctr(CID_SCon, STAT_OFF + 484), 97ull, term_ctr(CID_SCon, STAT_OFF + 486), 118ull, term_ctr(CID_SCon, STAT_OFF + 488), 99ull, term_ctr(CID_SCon, STAT_OFF + 490), 32ull, term_ctr(CID_SCon, STAT_OFF + 492), 69ull, term_ctr(CID_SCon, STAT_OFF + 494), 50ull, term_pak(CID_SNil, 0), 51ull, term_ctr(CID_SCon, STAT_OFF + 498), 85ull, term_ctr(CID_SCon, STAT_OFF + 500), 32ull, term_ctr(CID_SCon, STAT_OFF + 502), 108ull, term_ctr(CID_SCon, STAT_OFF + 504), 97ull, term_ctr(CID_SCon, STAT_OFF + 506), 109ull, term_ctr(CID_SCon, STAT_OFF + 508), 105ull, term_ctr(CID_SCon, STAT_OFF + 510), 99ull, term_ctr(CID_SCon, STAT_OFF + 512), 101ull, term_ctr(CID_SCon, STAT_OFF + 514), 100ull, term_ctr(CID_SCon, STAT_OFF + 516), 32ull, term_ctr(CID_SCon, STAT_OFF + 518), 97ull, term_ctr(CID_SCon, STAT_OFF + 520), 32ull, term_ctr(CID_SCon, STAT_OFF + 522), 115ull, term_ctr(CID_SCon, STAT_OFF + 524), 116ull, term_ctr(CID_SCon, STAT_OFF + 526), 110ull, term_ctr(CID_SCon, STAT_OFF + 528), 97ull, term_ctr(CID_SCon, STAT_OFF + 530), 119ull, term_ctr(CID_SCon, STAT_OFF + 532), 32ull, term_ctr(CID_SCon, STAT_OFF + 534), 110ull, term_ctr(CID_SCon, STAT_OFF + 536), 101ull, term_ctr(CID_SCon, STAT_OFF + 538), 112ull, term_ctr(CID_SCon, STAT_OFF + 540), 111ull, term_ctr(CID_SCon, STAT_OFF + 542), 32ull, term_ctr(CID_SCon, STAT_OFF + 544), 58ull, term_ctr(CID_SCon, STAT_OFF + 546), 111ull, term_ctr(CID_SCon, STAT_OFF + 548), 104ull, term_ctr(CID_SCon, STAT_OFF + 550), 99ull, term_ctr(CID_SCon, STAT_OFF + 552), 101ull, term_ctr(CID_SCon, STAT_OFF + 554), 32ull, term_ctr(CID_SCon, STAT_OFF + 556), 69ull, term_ctr(CID_SCon, STAT_OFF + 558), 100ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 562), 115ull, term_ctr(CID_SCon, STAT_OFF + 564), 117ull, term_ctr(CID_SCon, STAT_OFF + 566), 102ull, term_ctr(CID_SCon, STAT_OFF + 568), 101ull, term_ctr(CID_SCon, STAT_OFF + 570), 114ull, term_ctr(CID_SCon, STAT_OFF + 572), 32ull, term_ctr(CID_SCon, STAT_OFF + 574), 115ull, term_ctr(CID_SCon, STAT_OFF + 576), 97ull, term_ctr(CID_SCon, STAT_OFF + 578), 119ull, term_ctr(CID_SCon, STAT_OFF + 580), 32ull, term_ctr(CID_SCon, STAT_OFF + 582), 101ull, term_ctr(CID_SCon, STAT_OFF + 584), 108ull, term_ctr(CID_SCon, STAT_OFF + 586), 98ull, term_ctr(CID_SCon, STAT_OFF + 588), 97ull, term_ctr(CID_SCon, STAT_OFF + 590), 116ull, term_ctr(CID_SCon, STAT_OFF + 592), 32ull, term_ctr(CID_SCon, STAT_OFF + 594), 115ull, term_ctr(CID_SCon, STAT_OFF + 596), 115ull, term_ctr(CID_SCon, STAT_OFF + 598), 101ull, term_ctr(CID_SCon, STAT_OFF + 600), 114ull, term_ctr(CID_SCon, STAT_OFF + 602), 112ull, term_ctr(CID_SCon, STAT_OFF + 604), 32ull, term_ctr(CID_SCon, STAT_OFF + 606), 101ull, term_ctr(CID_SCon, STAT_OFF + 608), 104ull, term_ctr(CID_SCon, STAT_OFF + 610), 116ull, term_ctr(CID_SCon, STAT_OFF + 612), 32ull, term_ctr(CID_SCon, STAT_OFF + 614), 58ull, term_ctr(CID_SCon, STAT_OFF + 616), 114ull, term_ctr(CID_SCon, STAT_OFF + 618), 97ull, term_ctr(CID_SCon, STAT_OFF + 620), 118ull, term_ctr(CID_SCon, STAT_OFF + 622), 99ull, term_ctr(CID_SCon, STAT_OFF + 624), 32ull, term_ctr(CID_SCon, STAT_OFF + 626), 69ull, term_ctr(CID_SCon, STAT_OFF + 628), 32ull, term_pak(CID_SNil, 0), 110ull, term_ctr(CID_SCon, STAT_OFF + 584), 101ull, term_ctr(CID_SCon, STAT_OFF + 634), 112ull, term_ctr(CID_SCon, STAT_OFF + 636), 111ull, term_ctr(CID_SCon, STAT_OFF + 638), 32ull, term_ctr(CID_SCon, STAT_OFF + 640), 101ull, term_ctr(CID_SCon, STAT_OFF + 642), 104ull, term_ctr(CID_SCon, STAT_OFF + 644), 116ull, term_ctr(CID_SCon, STAT_OFF + 646), 32ull, term_ctr(CID_SCon, STAT_OFF + 648), 58ull, term_ctr(CID_SCon, STAT_OFF + 650), 111ull, term_ctr(CID_SCon, STAT_OFF + 652), 104ull, term_ctr(CID_SCon, STAT_OFF + 654), 99ull, term_ctr(CID_SCon, STAT_OFF + 656), 101ull, term_ctr(CID_SCon, STAT_OFF + 658), 32ull, term_ctr(CID_SCon, STAT_OFF + 660), 69ull, term_ctr(CID_SCon, STAT_OFF + 662), 114ull, term_ctr(CID_SCon, STAT_OFF + 300), 116ull, term_ctr(CID_SCon, STAT_OFF + 666), 110ull, term_ctr(CID_SCon, STAT_OFF + 668), 101ull, term_ctr(CID_SCon, STAT_OFF + 670), 32ull, term_ctr(CID_SCon, STAT_OFF + 672), 110ull, term_ctr(CID_SCon, STAT_OFF + 674), 119ull, term_ctr(CID_SCon, STAT_OFF + 676), 111ull, term_ctr(CID_SCon, STAT_OFF + 678), 110ull, term_ctr(CID_SCon, STAT_OFF + 680), 107ull, term_ctr(CID_SCon, STAT_OFF + 682), 110ull, term_ctr(CID_SCon, STAT_OFF + 684), 117ull, term_ctr(CID_SCon, STAT_OFF + 686), 32ull, term_ctr(CID_SCon, STAT_OFF + 688), 69ull, term_ctr(CID_SCon, STAT_OFF + 690), 108ull, term_pak(CID_SNil, 0), 108ull, term_ctr(CID_SCon, STAT_OFF + 694), 97ull, term_ctr(CID_SCon, STAT_OFF + 696), 99ull, term_ctr(CID_SCon, STAT_OFF + 698), 110ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 702), 112ull, term_ctr(CID_SCon, STAT_OFF + 704), 111ull, term_ctr(CID_SCon, STAT_OFF + 706), 93ull, term_pak(CID_SNil, 0), 46ull, term_ctr(CID_SCon, STAT_OFF + 710), 46ull, term_ctr(CID_SCon, STAT_OFF + 712), 46ull, term_ctr(CID_SCon, STAT_OFF + 714), 62ull, term_ctr(CID_SCon, STAT_OFF + 716), 116ull, term_ctr(CID_SCon, STAT_OFF + 718), 110ull, term_ctr(CID_SCon, STAT_OFF + 720), 101ull, term_ctr(CID_SCon, STAT_OFF + 722), 118ull, term_ctr(CID_SCon, STAT_OFF + 724), 101ull, term_ctr(CID_SCon, STAT_OFF + 726), 60ull, term_ctr(CID_SCon, STAT_OFF + 728), 91ull, term_ctr(CID_SCon, STAT_OFF + 730), 32ull, term_ctr(CID_SCon, STAT_OFF + 732), 62ull, term_ctr(CID_SCon, STAT_OFF + 734), 116ull, term_ctr(CID_SCon, STAT_OFF + 736), 117ull, term_ctr(CID_SCon, STAT_OFF + 738), 112ull, term_ctr(CID_SCon, STAT_OFF + 740), 110ull, term_ctr(CID_SCon, STAT_OFF + 742), 105ull, term_ctr(CID_SCon, STAT_OFF + 744), 60ull, term_ctr(CID_SCon, STAT_OFF + 746), 32ull, term_ctr(CID_SCon, STAT_OFF + 748), 62ull, term_ctr(CID_SCon, STAT_OFF + 750), 121ull, term_ctr(CID_SCon, STAT_OFF + 752), 114ull, term_ctr(CID_SCon, STAT_OFF + 754), 116ull, term_ctr(CID_SCon, STAT_OFF + 756), 110ull, term_ctr(CID_SCon, STAT_OFF + 758), 101ull, term_ctr(CID_SCon, STAT_OFF + 760), 60ull, term_ctr(CID_SCon, STAT_OFF + 762), 32ull, term_ctr(CID_SCon, STAT_OFF + 764), 110ull, term_ctr(CID_SCon, STAT_OFF + 766), 101ull, term_ctr(CID_SCon, STAT_OFF + 768), 112ull, term_ctr(CID_SCon, STAT_OFF + 770), 111ull, term_ctr(CID_SCon, STAT_OFF + 772), 32ull, term_ctr(CID_SCon, STAT_OFF + 774), 101ull, term_ctr(CID_SCon, STAT_OFF + 776), 114ull, term_ctr(CID_SCon, STAT_OFF + 778), 111ull, term_ctr(CID_SCon, STAT_OFF + 780), 99ull, term_ctr(CID_SCon, STAT_OFF + 782), 32ull, term_ctr(CID_SCon, STAT_OFF + 784), 124ull, term_ctr(CID_SCon, STAT_OFF + 786), 32ull, term_ctr(CID_SCon, STAT_OFF + 788), 62ull, term_ctr(CID_SCon, STAT_OFF + 790), 116ull, term_ctr(CID_SCon, STAT_OFF + 792), 117ull, term_ctr(CID_SCon, STAT_OFF + 794), 112ull, term_ctr(CID_SCon, STAT_OFF + 796), 110ull, term_ctr(CID_SCon, STAT_OFF + 798), 105ull, term_ctr(CID_SCon, STAT_OFF + 800), 60ull, term_ctr(CID_SCon, STAT_OFF + 802), 32ull, term_ctr(CID_SCon, STAT_OFF + 804), 62ull, term_ctr(CID_SCon, STAT_OFF + 806), 121ull, term_ctr(CID_SCon, STAT_OFF + 808), 114ull, term_ctr(CID_SCon, STAT_OFF + 810), 116ull, term_ctr(CID_SCon, STAT_OFF + 812), 110ull, term_ctr(CID_SCon, STAT_OFF + 814), 101ull, term_ctr(CID_SCon, STAT_OFF + 816), 60ull, term_ctr(CID_SCon, STAT_OFF + 818), 32ull, term_ctr(CID_SCon, STAT_OFF + 820), 108ull, term_ctr(CID_SCon, STAT_OFF + 822), 108ull, term_ctr(CID_SCon, STAT_OFF + 824), 97ull, term_ctr(CID_SCon, STAT_OFF + 826), 99ull, term_ctr(CID_SCon, STAT_OFF + 828), 32ull, term_ctr(CID_SCon, STAT_OFF + 830), 101ull, term_ctr(CID_SCon, STAT_OFF + 832), 114ull, term_ctr(CID_SCon, STAT_OFF + 834), 111ull, term_ctr(CID_SCon, STAT_OFF + 836), 99ull, term_ctr(CID_SCon, STAT_OFF + 838), 32ull, term_ctr(CID_SCon, STAT_OFF + 840), 58ull, term_ctr(CID_SCon, STAT_OFF + 842), 101ull, term_ctr(CID_SCon, STAT_OFF + 844), 103ull, term_ctr(CID_SCon, STAT_OFF + 846), 97ull, term_ctr(CID_SCon, STAT_OFF + 848), 115ull, term_ctr(CID_SCon, STAT_OFF + 850), 117ull, term_ctr(CID_SCon, STAT_OFF + 852) };

INLINE Term spin_0(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _r_1;
      o[3] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_3(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _f_3 = r0;
  Term _s_3 = r1;
  WL_SPIN
    if (_f_3 == 1) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_3;
    } else {
      term_sink(e, _s_3);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_2(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _t_3 = r0;
  u32 _f_2 = r1;
  Term _s_2 = r2;
  WL_SPIN
    if (_t_3 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_2;
    } else {
      Term _o_1[3];
      if (spin_3(e, _o_1, _f_2, _s_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = (u32)_o_1[1];
      o[2] = _o_1[2];
    }
  break;
  }
  return 1;
}

INLINE Term spin_1(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_1 = r0;
  WL_SPIN
    if (term_aux(_s_1) == CID_SNil) {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_1, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _o_2[3];
      if (spin_2(e, _o_2, U32_BIN(_f_0, ==, 84ull), U32_BIN(_f_0, ==, 70ull), _f_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_2[0];
      o[1] = (u32)_o_2[1];
      o[2] = _o_2[2];
      spare_free(e, cls_fit(2), _sp_0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_4(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_3 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  WL_SPIN
    if (_r_3 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _r_4;
      o[3] = _r_5;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_5(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _a_0 = r0;
  u32 _b_0 = r1;
  WL_SPIN
    o[0] = U32_BIN(_a_0, ==, _b_0);
  break;
  }
  return 1;
}

INLINE Term spin_6(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_1 = r0;
  WL_SPIN
    if (term_aux(_s_1) == CID_SNil) {
      o[0] = 1;
    } else {
      u64 _sp_0 = term_peek(e.mem, _s_1);
      u32 _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_7(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _i_0 = r0;
  u32 _r_4 = r1;
  u32 _r_5 = r2;
  Term _r_6 = r3;
  Term _r_7 = r4;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _i_0;
      o[3] = _r_5;
      o[4] = _r_6;
      o[5] = _r_7;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_8(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _a_0 = r0;
  u32 _b_0 = r1;
  WL_SPIN
    if (_a_0 == 0) {
      o[0] = 0;
    } else {
      o[0] = _b_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_9(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _t_0 = r0;
  Term _s_0 = r1;
  WL_SPIN
    if (_t_0 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = 0;
      o[3] = _s_0;
    } else if (_t_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = 1;
      o[3] = _s_0;
    } else if (_t_0 == 2) {
      o[0] = 0;
      o[1] = 1;
      o[2] = 2;
      o[3] = _s_0;
    } else {
      Term _x_0 = (_t_0 - 3);
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_12(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  Term _p_1 = r1;
  WL_SPIN
    o[0] = _p_0;
  break;
  }
  return 1;
}

INLINE Term spin_11(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _a_1 = (_b_0 == 0 ? 0 : _a_0 / _b_0);
    Term _a_2 = (_b_0 == 0 ? _a_0 : _a_0 % _b_0);
    Term _o_0[1];
    if (spin_12(e, _o_0, _a_1, _a_2) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_14(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_2 = r0;
  Term _p_3 = r1;
  WL_SPIN
    o[0] = _p_3;
  break;
  }
  return 1;
}

INLINE Term spin_13(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_3 = r0;
  Term _b_1 = r1;
  WL_SPIN
    Term _a_4 = (_b_1 == 0 ? 0 : _a_3 / _b_1);
    Term _a_5 = (_b_1 == 0 ? _a_3 : _a_3 % _b_1);
    Term _o_2[1];
    if (spin_14(e, _o_2, _a_4, _a_5) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_15(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _d_0 = r0;
  WL_SPIN
    if (_d_0 == 0) {
      o[0] = 48ull;
    } else if (_d_0 == 1) {
      o[0] = 49ull;
    } else if (_d_0 == 2) {
      o[0] = 50ull;
    } else if (_d_0 == 3) {
      o[0] = 51ull;
    } else if (_d_0 == 4) {
      o[0] = 52ull;
    } else if (_d_0 == 5) {
      o[0] = 53ull;
    } else if (_d_0 == 6) {
      o[0] = 54ull;
    } else if (_d_0 == 7) {
      o[0] = 55ull;
    } else if (_d_0 == 8) {
      o[0] = 56ull;
    } else if (_d_0 == 9) {
      o[0] = 57ull;
    } else {
      Term _p_4 = (_d_0 - 10);
      o[0] = 57ull;
    }
  break;
  }
  return 1;
}

INLINE Term spin_16(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _g_0 = r0;
  Term _n_1 = r1;
  Term _acc_0 = r2;
  WL_SPIN
    if (_g_0 == 0) {
      o[0] = _acc_0;
    } else {
      Term _f_0 = (_g_0 - 1);
      if (_n_1 == 0) {
        o[0] = _acc_0;
      } else {
        Term _p_5 = (_n_1 - 1);
        Term _m_0 = nat_chk(e, _p_5 + 1);
        Term _v_6 = 0;
        Term _o_5[1];
        if (spin_11(e, _o_5, _m_0, 10ull) == 0) {
          return 0;
        }
        _v_6 = _o_5[0];
        u32 _v_7 = 0;
        Term _v_8 = 0;
        Term _o_6[1];
        if (spin_13(e, _o_6, _m_0, 10ull) == 0) {
          return 0;
        }
        _v_8 = _o_6[0];
        Term _o_7[1];
        if (spin_15(e, _o_7, _v_8) == 0) {
          return 0;
        }
        _v_7 = (u32)_o_7[0];
        u64 _nd_2 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_2 + 0] = rfc_seal(e, _v_7);
        e.mem[_nd_2 + 1] = rfc_seal(e, _acc_0);
        r0 = _f_0;
        r1 = _v_6;
        r2 = term_ctr(CID_SCon, _nd_2);
        _g_0 = r0;
        _n_1 = r1;
        _acc_0 = r2;
        WL_AGAIN(spin_16);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_10(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    Term _v_3 = 0;
    Term _o_1[1];
    if (spin_11(e, _o_1, _n_0, 10ull) == 0) {
      return 0;
    }
    _v_3 = _o_1[0];
    u32 _v_4 = 0;
    Term _v_5 = 0;
    Term _o_3[1];
    if (spin_13(e, _o_3, _n_0, 10ull) == 0) {
      return 0;
    }
    _v_5 = _o_3[0];
    Term _o_4[1];
    if (spin_15(e, _o_4, _v_5) == 0) {
      return 0;
    }
    _v_4 = (u32)_o_4[0];
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, 44ull);
    e.mem[_nd_0 + 1] = rfc_seal(e, _rest_1);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _v_4);
    e.mem[_nd_1 + 1] = rfc_seal(e, term_ctr(CID_SCon, _nd_0));
    Term _o_8[1];
    if (spin_16(e, _o_8, _n_0, _v_3, term_ctr(CID_SCon, _nd_1)) == 0) {
      return 0;
    }
    o[0] = _o_8[0];
  break;
  }
  return 1;
}

INLINE Term spin_17(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _b_2 = r0;
  Term _rest_2 = r1;
  WL_SPIN
    if (_b_2 == 1) {
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, 84ull);
      e.mem[_nd_3 + 1] = rfc_seal(e, _rest_2);
      o[0] = term_ctr(CID_SCon, _nd_3);
    } else {
      u64 _nd_4 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_4 + 0] = rfc_seal(e, 70ull);
      e.mem[_nd_4 + 1] = rfc_seal(e, _rest_2);
      o[0] = term_ctr(CID_SCon, _nd_4);
    }
  break;
  }
  return 1;
}

INLINE Term spin_18(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _r_1;
      o[3] = 0;
      o[4] = 0;
      o[5] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_19(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_3 = r0;
  Term _r_4 = r1;
  Term _r_5 = r2;
  WL_SPIN
    if (_r_3 == 0) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _r_4;
      o[3] = 0;
      o[4] = 0;
      o[5] = _r_5;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_20(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_6 = r0;
  Term _r_7 = r1;
  Term _r_8 = r2;
  WL_SPIN
    if (_r_6 == 0) {
      o[0] = 0;
      o[1] = 3;
      o[2] = _r_7;
      o[3] = 0;
      o[4] = 0;
      o[5] = _r_8;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_23(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _a_2 = r0;
  Term _b_2 = r1;
  u32 _c_0 = r2;
  WL_SPIN
    if (term_aux(_a_2) == CID_SNil) {
      if (term_aux(_b_2) == CID_SCon) {
        Term _fb_1[2];
        u64 _sp_1 = ctr_take(e, _b_2, 2, _fb_1);
        u32 _f_2 = _fb_1[0];
        Term _f_3 = _fb_1[1];
        term_sink(e, _f_3);
        if (_c_0 == 1) {
          o[0] = 0;
          spare_free(e, cls_fit(2), _sp_1);
        } else {
          o[0] = _c_0;
          spare_free(e, cls_fit(2), _sp_1);
        }
      } else {
        term_sink(e, _b_2);
        o[0] = _c_0;
      }
    } else {
      Term _fb_2[2];
      u64 _sp_2 = ctr_take(e, _a_2, 2, _fb_2);
      u32 _f_4 = _fb_2[0];
      Term _f_5 = _fb_2[1];
      if (term_aux(_b_2) == CID_SNil) {
        term_sink(e, _f_5);
        if (_c_0 == 1) {
          o[0] = 2;
          spare_free(e, cls_fit(2), _sp_2);
        } else {
          o[0] = _c_0;
          spare_free(e, cls_fit(2), _sp_2);
        }
      } else {
        Term _fb_3[2];
        u64 _sp_3 = ctr_take(e, _b_2, 2, _fb_3);
        u32 _f_6 = _fb_3[0];
        Term _f_7 = _fb_3[1];
        if (_c_0 == 1) {
          spare_free(e, cls_fit(2), _sp_3);
          spare_free(e, cls_fit(2), _sp_2);
          r0 = _f_5;
          r1 = _f_7;
          r2 = (U32_BIN(_f_4, >, _f_6) + U32_BIN(_f_4, >=, _f_6));
          _a_2 = r0;
          _b_2 = r1;
          _c_0 = r2;
          WL_AGAIN(spin_23);
        } else {
          term_sink(e, _f_5);
          term_sink(e, _f_7);
          o[0] = _c_0;
          spare_free(e, cls_fit(2), _sp_3);
          spare_free(e, cls_fit(2), _sp_2);
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_22(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_1 = r0;
  Term _b_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_23(e, _o_0, _a_1, _b_1, 1) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_24(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _c_1 = r0;
  WL_SPIN
    if (_c_1 == 1) {
      o[0] = 1;
    } else {
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_21(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    u32 _v_0 = 0;
    Term _o_1[1];
    if (spin_22(e, _o_1, _a_0, _b_0) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    Term _o_2[1];
    if (spin_24(e, _o_2, _v_0) == 0) {
      return 0;
    }
    o[0] = (u32)_o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_25(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _ns_1 = r0;
  Term _u_1 = r1;
  WL_SPIN
    if (term_aux(_ns_1) == CID_Nil) {
      term_sink(e, _u_1);
      o[0] = 0;
    } else {
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _ns_1, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      term_sink(e, _f_3);
      Term _o_0[1];
      if (spin_21(e, _o_0, _f_2, _u_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      spare_free(e, cls_fit(2), _sp_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_27(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _ns_1 = r0;
  Term _u_1 = r1;
  u32 _hit_1 = r2;
  WL_SPIN
    if (term_aux(_ns_1) == CID_Nil) {
      term_sink(e, _u_1);
      o[0] = 0;
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ns_1, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      term_sink(e, _f_0);
      if (_hit_1 == 1) {
        term_sink(e, _f_1);
        term_sink(e, _u_1);
        o[0] = 1;
        spare_free(e, cls_fit(2), _sp_0);
      } else {
        u32 _v_1 = 0;
        _f_1 = term_keep(e, _f_1, 1);
        _u_1 = term_keep(e, _u_1, 1);
        Term _o_1[1];
        if (spin_25(e, _o_1, _f_1, _u_1) == 0) {
          return 0;
        }
        _v_1 = (u32)_o_1[0];
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _u_1;
        r2 = _v_1;
        _ns_1 = r0;
        _u_1 = r1;
        _hit_1 = r2;
        WL_AGAIN(spin_27);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_26(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _ns_0 = r0;
  Term _u_0 = r1;
  WL_SPIN
    u32 _v_0 = 0;
    _ns_0 = term_keep(e, _ns_0, 1);
    _u_0 = term_keep(e, _u_0, 1);
    Term _o_0[1];
    if (spin_25(e, _o_0, _ns_0, _u_0) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    Term _o_2[1];
    if (spin_27(e, _o_2, _ns_0, _u_0, _v_0) == 0) {
      return 0;
    }
    o[0] = (u32)_o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_28(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _c_1 = r0;
  WL_SPIN
    Term _o_0[1];
    if (spin_8(e, _o_0, U32_BIN(_c_1, >=, 97ull), U32_BIN(_c_1, <=, 122ull)) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_29(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  WL_SPIN
    if (_b_0 == 0) {
      o[0] = 0ull;
    } else {
      o[0] = 1ull;
    }
  break;
  }
  return 1;
}

INLINE Term spin_30(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _k_0;
      o[2] = _r_5;
      o[3] = _r_6;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_31(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      Term _o_0[4];
      if (spin_9(e, _o_0, _r_1, _r_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = (u32)_o_0[1];
      o[2] = (u32)_o_0[2];
      o[3] = _o_0[3];
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_32(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 3;
      o[2] = _r_1;
      o[3] = _r_2;
      o[4] = _r_3;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_33(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  Term _l_2 = r0;
  Term _l_3 = r1;
  u32 _d_2 = r2;
  Term _d_3 = r3;
  WL_SPIN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _l_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _l_3);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_0));
    e.mem[_nd_1 + 1] = rfc_seal(e, _d_3);
    o[0] = _d_2;
    o[1] = term_ctr(CID_Con, _nd_1);
  break;
  }
  return 1;
}

INLINE Term spin_34(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _room_1 = r0;
  Term _l_2 = r1;
  Term _l_3 = r2;
  Term _n_2 = r3;
  Term _n_3 = r4;
  Term _rest_1 = r5;
  WL_SPIN
    if (_room_1 == 1) {
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _l_2);
      e.mem[_nd_2 + 1] = rfc_seal(e, _l_3);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _rest_1);
      u64 _nd_4 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_4 + 0] = rfc_seal(e, _n_2);
      e.mem[_nd_4 + 1] = rfc_seal(e, _n_3);
      u64 _nd_5 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_5 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_4));
      e.mem[_nd_5 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_3));
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_5);
    } else {
      u64 _nd_6 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_6 + 0] = rfc_seal(e, _l_2);
      e.mem[_nd_6 + 1] = rfc_seal(e, _l_3);
      u64 _nd_7 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_7 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_6));
      e.mem[_nd_7 + 1] = rfc_seal(e, _rest_1);
      o[0] = 2;
      o[1] = term_ctr(CID_Con, _nd_7);
    }
  break;
  }
  return 1;
}

INLINE Term spin_35(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _v_2 = r0;
  Term _v_3 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    if (_v_2 == 0) {
      Term _v_4 = 0;
      Term _o_0[1];
      if (spin_10(e, _o_0, _v_3, _rest_1) == 0) {
        return 0;
      }
      _v_4 = _o_0[0];
      Term _o_1[1];
      if (spin_10(e, _o_1, 0, _v_4) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _v_5 = 0;
      Term _o_2[1];
      if (spin_17(e, _o_2, _v_3, _rest_1) == 0) {
        return 0;
      }
      _v_5 = _o_2[0];
      Term _o_3[1];
      if (spin_10(e, _o_3, 1ull, _v_5) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_36(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  u32 _r_0 = r1;
  Term _r_1 = r2;
  Term _r_2 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_1 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_1);
      o[2] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_37(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _r_0 = r1;
  Term _r_1 = r2;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_10(e, _o_0, _x_0, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_38(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  Term _r_0 = r1;
  Term _r_1 = r2;
  WL_SPIN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _c_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, _r_1);
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = term_ctr(CID_SCon, _nd_0);
  break;
  }
  return 1;
}

INLINE Term spin_39(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _n_0;
      o[2] = _r_5;
      o[3] = _r_6;
    } else {
      term_sink(e, _n_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_40(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _v_2 = r0;
  Term _v_3 = r1;
  WL_SPIN
    term_sink(e, _v_3);
    o[0] = _v_2;
  break;
  }
  return 1;
}

INLINE Term spin_41(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _hit_1 = r0;
  Term _keep_2 = r1;
  Term _n_2 = r2;
  WL_SPIN
    if (_hit_1 == 1) {
      Term _o_0[1];
      if (spin_26(e, _o_0, _keep_2, _n_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
    } else {
      term_sink(e, _keep_2);
      term_sink(e, _n_2);
      o[0] = 1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_42(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  WL_SPIN
    u32 _v_1 = 0;
    u32 _v_2 = 0;
    Term _o_0[1];
    if (spin_28(e, _o_0, _c_0) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_29(e, _o_1, _v_2) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_1[0];
    o[0] = U32_BIN(_c_0, -, U32_BIN(_v_1, *, 32ull));
  break;
  }
  return 1;
}

INLINE Term spin_43(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  u32 _r_0 = r2;
  Term _r_1 = r3;
  Term _r_2 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_3);
      o[2] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_44(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _l_0 = r0;
  Term _l_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    if (_l_1 == 0) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _l_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, 0);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _rest_0);
      o[0] = 1;
      o[1] = term_ctr(CID_Con, _nd_1);
    } else {
      Term _c_0 = (_l_1 - 1);
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _l_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _c_0);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _rest_0);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_3);
    }
  break;
  }
  return 1;
}

INLINE Term spin_45(Env e, THR Term* o, Term r0, Term r1, Term r2, Term r3, Term r4, u32 r5) {
  u32 wpoll = 0;
  Term _l_2 = r0;
  Term _l_3 = r1;
  Term _n_0 = r2;
  Term _n_1 = r3;
  Term _rest_1 = r4;
  u32 _room_1 = r5;
  WL_SPIN
    if (_l_3 == 0) {
      u64 _nd_6 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_6 + 0] = rfc_seal(e, _l_2);
      e.mem[_nd_6 + 1] = rfc_seal(e, 0);
      u64 _nd_7 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_7 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_6));
      e.mem[_nd_7 + 1] = rfc_seal(e, _rest_1);
      o[0] = 1;
      o[1] = term_ctr(CID_Con, _nd_7);
    } else {
      Term _c_1 = (_l_3 - 1);
      Term _o_6[2];
      if (spin_34(e, _o_6, _room_1, _l_2, _c_1, _n_0, _n_1, _rest_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_6[0];
      o[1] = _o_6[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_46(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4) {
  u32 wpoll = 0;
  u32 _stay_2 = r0;
  Term _l_4 = r1;
  Term _l_5 = r2;
  u32 _d_0 = r3;
  Term _d_1 = r4;
  WL_SPIN
    if (_stay_2 == 1) {
      Term _o_8[2];
      if (spin_33(e, _o_8, _l_4, _l_5, _d_0, _d_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_8[0];
      o[1] = _o_8[1];
    } else {
      o[0] = _d_0;
      o[1] = _d_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_47(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _l_0 = r0;
  Term _l_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    Term _v_1 = 0;
    Term _o_0[1];
    if (spin_10(e, _o_0, _l_1, _rest_0) == 0) {
      return 0;
    }
    _v_1 = _o_0[0];
    Term _o_1[1];
    if (spin_10(e, _o_1, _l_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_48(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_24(e, _o_0, ((_a_0 > _b_0) + (_a_0 >= _b_0))) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_49(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _as_1 = r0;
  Term _n_1 = r1;
  WL_SPIN
    if (term_aux(_as_1) == CID_Nil) {
      o[0] = 0;
    } else {
      u64 _sp_2 = term_peek(e.mem, _as_1);
      Term _f_4 = e.mem[_sp_2 + 0];
      Term _f_5 = e.mem[_sp_2 + 1];
      u64 _sp_3 = term_peek(e.mem, _f_4);
      Term _f_6 = e.mem[_sp_3 + 0];
      Term _f_7 = e.mem[_sp_3 + 1];
      Term _o_0[1];
      if (spin_48(e, _o_0, _f_6, _n_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_50(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  Term _c_1 = r1;
  u32 _c_2 = r2;
  Term _c_3 = r3;
  Term _rest_0 = r4;
  WL_SPIN
    if (_c_0 == 0) {
      Term _v_1 = 0;
      Term _v_2 = 0;
      Term _o_0[1];
      if (spin_35(e, _o_0, _c_2, _c_3, _rest_0) == 0) {
        return 0;
      }
      _v_2 = _o_0[0];
      Term _o_1[1];
      if (spin_10(e, _o_1, _c_1, _v_2) == 0) {
        return 0;
      }
      _v_1 = _o_1[0];
      Term _o_2[1];
      if (spin_10(e, _o_2, 0, _v_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else if (_c_0 == 1) {
      Term _v_3 = 0;
      Term _o_3[1];
      if (spin_10(e, _o_3, _c_1, _rest_0) == 0) {
        return 0;
      }
      _v_3 = _o_3[0];
      Term _o_4[1];
      if (spin_10(e, _o_4, 1ull, _v_3) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    } else if (_c_0 == 2) {
      Term _v_4 = 0;
      Term _o_5[1];
      if (spin_10(e, _o_5, _c_1, _rest_0) == 0) {
        return 0;
      }
      _v_4 = _o_5[0];
      Term _o_6[1];
      if (spin_10(e, _o_6, 2ull, _v_4) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    } else {
      Term _v_5 = 0;
      Term _o_7[1];
      if (spin_10(e, _o_7, _c_1, _rest_0) == 0) {
        return 0;
      }
      _v_5 = _o_7[0];
      Term _o_8[1];
      if (spin_10(e, _o_8, 3ull, _v_5) == 0) {
        return 0;
      }
      o[0] = _o_8[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_51(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, u32 r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  Term _x_1 = r1;
  u32 _x_2 = r2;
  Term _x_3 = r3;
  u32 _r_0 = r4;
  Term _r_1 = r5;
  Term _r_2 = r6;
  WL_SPIN
    if (_r_0 == 0) {
      Term _b_1 = 0;
      if (_x_0 == 0) {
        u64 _nd_5 = heap_alloc(e, cls_fit(3));
        e.mem[_nd_5 + 0] = rfc_seal(e, _x_1);
        e.mem[_nd_5 + 1] = rfc_seal(e, _x_2);
        e.mem[_nd_5 + 2] = rfc_seal(e, _x_3);
        _b_1 = term_ctr(CID_cvar_CSet, _nd_5);
      } else if (_x_0 == 1) {
        u64 _nd_6 = heap_alloc(e, cls_fit(1));
        e.mem[_nd_6 + 0] = rfc_seal(e, _x_1);
        _b_1 = term_ctr(CID_cvar_CToggle, _nd_6);
      } else if (_x_0 == 2) {
        u64 _nd_7 = heap_alloc(e, cls_fit(1));
        e.mem[_nd_7 + 0] = rfc_seal(e, _x_1);
        _b_1 = term_ctr(CID_cvar_CRun, _nd_7);
      } else {
        u64 _nd_8 = heap_alloc(e, cls_fit(1));
        e.mem[_nd_8 + 0] = rfc_seal(e, _x_1);
        _b_1 = term_ctr(CID_cvar_CGone, _nd_8);
      }
      u64 _nd_9 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_9 + 0] = rfc_seal(e, _b_1);
      e.mem[_nd_9 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_9);
      o[2] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_52(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _r_0 = r0;
  Term _r_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_10(e, _o_0, _r_0, _r_1) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_53(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _r_0 = r0;
  Term _r_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_10(e, _o_0, _r_0, _r_1) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_54(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  u32 _r_0 = r1;
  Term _r_1 = r2;
  Term _r_2 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _c_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_SCon, _nd_0);
      o[2] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_55(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  u32 _r_0 = r2;
  Term _r_1 = r3;
  Term _r_2 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_child_env_Var, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_3);
      o[2] = _r_2;
    } else {
      term_sink(e, _x_0);
      term_sink(e, _x_1);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_56(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _hit_0 = r0;
  Term _v_1 = r1;
  Term _v_2 = r2;
  Term _r_0 = r3;
  WL_SPIN
    if (_hit_0 == 1) {
      term_sink(e, _v_1);
      term_sink(e, _v_2);
      o[0] = _r_0;
    } else {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _v_1);
      e.mem[_nd_0 + 1] = rfc_seal(e, _v_2);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_child_env_Var, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _r_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_57(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  Term _x_1 = r1;
  Term _x_2 = r2;
  u32 _r_0 = r3;
  Term _r_1 = r4;
  Term _r_2 = r5;
  WL_SPIN
    if (_r_0 == 0) {
      Term _b_1 = 0;
      if (_x_0 == 0) {
        _b_1 = term_pak(CID_director_Defer, 0);
      } else if (_x_0 == 1) {
        _b_1 = term_pak(CID_director_Again, 0);
      } else if (_x_0 == 2) {
        _b_1 = term_pak(CID_director_Yield, 0);
      } else if (_x_0 == 3) {
        u64 _nd_2 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_2 + 0] = rfc_seal(e, _x_1);
        e.mem[_nd_2 + 1] = rfc_seal(e, _x_2);
        _b_1 = term_ctr(CID_director_Stack, _nd_2);
      } else if (_x_0 == 4) {
        _b_1 = term_pak(CID_director_Leave, 0);
      } else if (_x_0 == 5) {
        _b_1 = term_pak(CID_director_Abort, 0);
      } else {
        _b_1 = term_pak(CID_director_Lead, 0);
      }
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, _b_1);
      e.mem[_nd_3 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_3);
      o[2] = _r_2;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_58(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _d_0 = r0;
  Term _d_1 = r1;
  WL_SPIN
    o[0] = _d_1;
  break;
  }
  return 1;
}

INLINE Term spin_59(Env e, THR Term* o, Term r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  Term _r_0 = r2;
  Term _r_1 = r3;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_47(e, _o_0, _x_0, _x_1, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_60(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _as_1 = r0;
  Term _n_1 = r1;
  u32 _hit_0 = r2;
  WL_SPIN
    if (term_aux(_as_1) == CID_Nil) {
      u64 _nd_0 = heap_alloc(e, cls_fit(1));
      e.mem[_nd_0 + 0] = rfc_seal(e, _n_1);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_cvar_CGone, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
      o[0] = term_ctr(CID_Con, _nd_1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _as_1, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      if (_hit_0 == 1) {
        term_sink(e, _f_1);
        o[0] = _f_3;
        spare_free(e, cls_fit(2), _sp_0);
      } else {
        term_sink(e, _f_3);
        u32 _v_1 = 0;
        Term _o_1[1];
        if (spin_49(e, _o_1, _f_1, _n_1) == 0) {
          return 0;
        }
        _v_1 = (u32)_o_1[0];
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _n_1;
        r2 = _v_1;
        _as_1 = r0;
        _n_1 = r1;
        _hit_0 = r2;
        WL_AGAIN(spin_60);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_61(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  Term _x_1 = r1;
  u32 _x_2 = r2;
  Term _x_3 = r3;
  Term _r_0 = r4;
  Term _r_1 = r5;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_8[1];
    if (spin_50(e, _o_8, _x_0, _x_1, _x_2, _x_3, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_8[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_62(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _n_0;
      o[2] = _r_5;
      o[3] = _r_6;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_63(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _x_3 = r0;
  Term _rest_0 = r1;
  WL_SPIN
    Term _o_1[1];
    if (spin_10(e, _o_1, ((u64)_x_3), _rest_0) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_65(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _text_0 = r0;
  WL_SPIN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, 32ull);
    e.mem[_nd_0 + 1] = rfc_seal(e, _text_0);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, 69ull);
    e.mem[_nd_1 + 1] = rfc_seal(e, term_ctr(CID_SCon, _nd_0));
    o[0] = term_ctr(CID_SCon, _nd_1);
  break;
  }
  return 1;
}

INLINE Term spin_64(Env e, THR Term* o) {
  u32 wpoll = 0;
  WL_SPIN
    Term _o_4[1];
    if (spin_65(e, _o_4, term_ctr(CID_SCon, STAT_OFF + 196)) == 0) {
      return 0;
    }
    o[0] = _o_4[0];
  break;
  }
  return 1;
}

INLINE Term spin_66(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _ok_0 = r0;
  Term _v_1 = r1;
  Term _v_2 = r2;
  Term _r_0 = r3;
  WL_SPIN
    if (_ok_0 == 1) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _v_1);
      e.mem[_nd_0 + 1] = rfc_seal(e, _v_2);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_child_env_Var, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _r_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    } else {
      term_sink(e, _v_1);
      term_sink(e, _v_2);
      o[0] = _r_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_67(Env e, THR Term* o, Term r0, Term r1, u32 r2, u32 r3, u32 r4, Term r5) {
  u32 wpoll = 0;
  Term _n_2 = r0;
  Term _st_0 = r1;
  u32 _r_4 = r2;
  u32 _r_5 = r3;
  u32 _r_6 = r4;
  Term _r_7 = r5;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _n_2;
      o[2] = _st_0;
      o[3] = _r_5;
      o[4] = _r_6;
      o[5] = _r_7;
    } else {
      term_sink(e, _st_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_68(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _o_1 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    if (_o_1 == 0) {
      Term _o_2[1];
      if (spin_10(e, _o_2, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else if (_o_1 == 1) {
      Term _o_3[1];
      if (spin_10(e, _o_3, 1ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    } else {
      Term _o_4[1];
      if (spin_10(e, _o_4, 2ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_69(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _n_0;
      o[2] = _r_5;
      o[3] = _r_6;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_70(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _bs_1 = r0;
  Term _k_1 = r1;
  WL_SPIN
    if (term_aux(_bs_1) == CID_Nil) {
      o[0] = 0;
    } else {
      u64 _sp_2 = term_peek(e.mem, _bs_1);
      Term _f_4 = e.mem[_sp_2 + 0];
      Term _f_5 = e.mem[_sp_2 + 1];
      u64 _sp_3 = term_peek(e.mem, _f_4);
      Term _f_6 = e.mem[_sp_3 + 0];
      Term _f_7 = e.mem[_sp_3 + 1];
      Term _o_0[1];
      if (spin_48(e, _o_0, _f_6, _k_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_71(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _as_1 = r0;
  Term _n_0 = r1;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_8[1];
    if (spin_49(e, _o_8, _as_1, _n_0) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_8[0];
    Term _o_9[1];
    if (spin_60(e, _o_9, _as_1, _n_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_9[0];
  break;
  }
  return 1;
}

INLINE Term spin_72(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _xs_0 = r0;
  Term _acc_0 = r1;
  WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      o[0] = _acc_0;
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u32 _o_0 = 0;
      Term _o_1 = 0;
      u32 _o_2 = 0;
      Term _o_3 = 0;
      if (term_aux(_f_0) == CID_cvar_CSet) {
        _o_0 = 0;
        Term _fb_1[3];
        u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
        Term _f_2 = _fb_1[0];
        u32 _f_3 = _fb_1[1];
        Term _f_4 = _fb_1[2];
        spare_free(e, cls_fit(3), _sp_1);
        _o_1 = _f_2;
        _o_2 = _f_3;
        _o_3 = _f_4;
      } else if (term_aux(_f_0) == CID_cvar_CToggle) {
        _o_0 = 1;
        Term _fb_2[1];
        u64 _sp_2 = ctr_take(e, _f_0, 1, _fb_2);
        Term _f_5 = _fb_2[0];
        spare_free(e, cls_fit(1), _sp_2);
        _o_1 = _f_5;
      } else if (term_aux(_f_0) == CID_cvar_CRun) {
        _o_0 = 2;
        Term _fb_3[1];
        u64 _sp_3 = ctr_take(e, _f_0, 1, _fb_3);
        Term _f_6 = _fb_3[0];
        spare_free(e, cls_fit(1), _sp_3);
        _o_1 = _f_6;
      } else {
        _o_0 = 3;
        Term _fb_4[1];
        u64 _sp_4 = ctr_take(e, _f_0, 1, _fb_4);
        Term _f_7 = _fb_4[0];
        spare_free(e, cls_fit(1), _sp_4);
        _o_1 = _f_7;
      }
      Term _b_0 = 0;
      if (_o_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(3));
        e.mem[_nd_0 + 0] = rfc_seal(e, _o_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _o_2);
        e.mem[_nd_0 + 2] = rfc_seal(e, _o_3);
        _b_0 = term_ctr(CID_cvar_CSet, _nd_0);
      } else if (_o_0 == 1) {
        u64 _nd_1 = heap_alloc(e, cls_fit(1));
        e.mem[_nd_1 + 0] = rfc_seal(e, _o_1);
        _b_0 = term_ctr(CID_cvar_CToggle, _nd_1);
      } else if (_o_0 == 2) {
        u64 _nd_2 = heap_alloc(e, cls_fit(1));
        e.mem[_nd_2 + 0] = rfc_seal(e, _o_1);
        _b_0 = term_ctr(CID_cvar_CRun, _nd_2);
      } else {
        u64 _nd_3 = heap_alloc(e, cls_fit(1));
        e.mem[_nd_3 + 0] = rfc_seal(e, _o_1);
        _b_0 = term_ctr(CID_cvar_CGone, _nd_3);
      }
      u64 _nd_4 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
      e.mem[_nd_4 + 0] = rfc_seal(e, _b_0);
      e.mem[_nd_4 + 1] = rfc_seal(e, _acc_0);
      r0 = _f_1;
      r1 = term_ctr(CID_Con, _nd_4);
      _xs_0 = r0;
      _acc_0 = r1;
      WL_AGAIN(spin_72);
    }
  break;
  }
  return 1;
}

INLINE Term spin_73(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  u32 _r_0 = r2;
  Term _r_1 = r3;
  Term _r_2 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_cvar_Alias, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_3);
      o[2] = _r_2;
    } else {
      term_sink(e, _x_1);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_74(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _hit_0 = r0;
  u32 _later_0 = r1;
  Term _later_1 = r2;
  Term _i_2 = r3;
  WL_SPIN
    if (_hit_0 == 1) {
      o[0] = 1;
      o[1] = _i_2;
    } else {
      o[0] = _later_0;
      o[1] = _later_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_75(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _comma_1 = r0;
  WL_SPIN
    if (_comma_1 == 1) {
      o[0] = 1;
      o[1] = 0;
    } else {
      o[0] = 2;
      o[1] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_76(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  u32 _r_0 = r1;
  Term _r_1 = r2;
  Term _r_2 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_1 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_1);
      o[2] = _r_2;
    } else {
      term_sink(e, _x_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_77(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, Term r5) {
  u32 wpoll = 0;
  Term _r_2 = r0;
  Term _k_2 = r1;
  Term _b_0 = r2;
  u32 _d_4 = r3;
  Term _d_5 = r4;
  Term _d_6 = r5;
  WL_SPIN
    if (_d_4 == 0) {
      o[0] = 0;
      o[1] = _r_2;
      o[2] = _k_2;
      o[3] = _b_0;
      o[4] = _d_5;
      o[5] = _d_6;
    } else {
      term_sink(e, _r_2);
      term_sink(e, _k_2);
      term_sink(e, _b_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_78(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _e_0 = r0;
  u32 _e_1 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    if (_e_0 == 0) {
      Term _o_0[1];
      if (spin_10(e, _o_0, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else {
      Term _v_1 = 0;
      Term _o_1[1];
      if (spin_68(e, _o_1, _e_1, _rest_1) == 0) {
        return 0;
      }
      _v_1 = _o_1[0];
      Term _o_2[1];
      if (spin_10(e, _o_2, 1ull, _v_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_79(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  u32 _r_0 = r2;
  Term _r_1 = r3;
  Term _r_2 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_cvar_KeyBind, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _r_1);
      o[0] = 0;
      o[1] = term_ctr(CID_Con, _nd_3);
      o[2] = _r_2;
    } else {
      term_sink(e, _x_1);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_80(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _bs_1 = r0;
  Term _k_1 = r1;
  u32 _hit_0 = r2;
  WL_SPIN
    if (term_aux(_bs_1) == CID_Nil) {
      o[0] = term_pak(CID_Nil, 0);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _bs_1, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      if (_hit_0 == 1) {
        term_sink(e, _f_1);
        o[0] = _f_3;
        spare_free(e, cls_fit(2), _sp_0);
      } else {
        term_sink(e, _f_3);
        u32 _v_1 = 0;
        Term _o_1[1];
        if (spin_70(e, _o_1, _f_1, _k_1) == 0) {
          return 0;
        }
        _v_1 = (u32)_o_1[0];
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _k_1;
        r2 = _v_1;
        _bs_1 = r0;
        _k_1 = r1;
        _hit_0 = r2;
        WL_AGAIN(spin_80);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_81(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _e_0 = r0;
  Term _e_1 = r1;
  WL_SPIN
    if (_e_0 == 0) {
      Term _v_0 = 0;
      Term _o_0[1];
      if (spin_72(e, _o_0, _e_1, term_pak(CID_Nil, 0)) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      o[0] = 0;
      o[1] = _v_0;
    } else if (_e_0 == 1) {
      o[0] = 1;
      o[1] = _e_1;
    } else {
      o[0] = 2;
      o[1] = _e_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_82(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _qr_0 = r0;
  Term _qr_1 = r1;
  WL_SPIN
    o[0] = ((u64)(u32)(nat_chk(e, 48ull + _qr_1)));
    o[1] = _qr_0;
  break;
  }
  return 1;
}

INLINE Term spin_83(Env e, THR Term* o, u32 r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  u32 _comma_0 = r2;
  WL_SPIN
    if (_m_0 == 1) {
      o[0] = 0;
      o[1] = _m_1;
    } else {
      Term _o_0[2];
      if (spin_75(e, _o_0, _comma_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_84(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _ok_0 = r0;
  u32 _x_1 = r1;
  Term _s_0 = r2;
  WL_SPIN
    if (_ok_0 == 1) {
      o[0] = 0;
      o[1] = _x_1;
      o[2] = _s_0;
    } else {
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_85(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, u32 r4, u32 r5, Term r6, Term r7) {
  u32 wpoll = 0;
  Term _c_2 = r0;
  Term _l_0 = r1;
  Term _l_1 = r2;
  u32 _l_2 = r3;
  u32 _l_3 = r4;
  u32 _r_10 = r5;
  Term _r_11 = r6;
  Term _r_12 = r7;
  WL_SPIN
    if (_r_10 == 0) {
      o[0] = 0;
      o[1] = _c_2;
      o[2] = _l_0;
      o[3] = _l_1;
      o[4] = _l_2;
      o[5] = _l_3;
      o[6] = _r_11;
      o[7] = _r_12;
    } else {
      term_sink(e, _l_1);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
      o[7] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_86(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _bs_1 = r0;
  Term _k_1 = r1;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_70(e, _o_0, _bs_1, _k_1) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_80(e, _o_1, _bs_1, _k_1, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_87(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _as_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _as_0;
      o[2] = _r_5;
      o[3] = _r_6;
    } else {
      term_sink(e, _as_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_88(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _x_0 = ((u64)(u32)(_r_1));
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_48(e, _o_0, ((u64)_x_0), _r_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[3];
      if (spin_84(e, _o_1, _v_0, _x_0, _r_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = (u32)_o_1[1];
      o[2] = _o_1[2];
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_89(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _bs_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _bs_0;
      o[3] = _r_5;
      o[4] = _r_6;
    } else {
      term_sink(e, _bs_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_90(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_0 = r0;
  WL_SPIN
    Term _o_0[1];
    if (spin_6(e, _o_0, _s_0) == 0) {
      return 0;
    }
    term_sink(e, _s_0);
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_91(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3) {
  u32 wpoll = 0;
  u32 _t_0 = r0;
  Term _t_1 = r1;
  Term _t_2 = r2;
  u32 _done_0 = r3;
  WL_SPIN
    if (_done_0 == 1) {
      o[0] = _t_0;
      o[1] = _t_1;
      o[2] = _t_2;
      o[3] = term_pak(CID_SNil, 0);
    } else {
      term_sink(e, _t_1);
      term_sink(e, _t_2);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = term_ctr(CID_SCon, STAT_OFF + 298);
    }
  break;
  }
  return 1;
}

INLINE Term spin_92(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  Term _r_4 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_90(e, _o_0, _r_4) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[4];
      if (spin_91(e, _o_1, _r_1, _r_2, _r_3, _v_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = _o_1[1];
      o[2] = _o_1[2];
      o[3] = _o_1[3];
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = term_ctr(CID_SCon, STAT_OFF + 496);
    }
  break;
  }
  return 1;
}

INLINE Term spin_93(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  WL_SPIN
    o[0] = 0;
    o[1] = _r_0;
    o[2] = _r_1;
    o[3] = _r_2;
    o[4] = _r_3;
  break;
  }
  return 1;
}

INLINE Term spin_94(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_4 = r0;
  Term _r_5 = r1;
  Term _r_6 = r2;
  Term _r_7 = r3;
  WL_SPIN
    o[0] = 1;
    o[1] = _r_4;
    o[2] = _r_5;
    o[3] = _r_6;
    o[4] = _r_7;
  break;
  }
  return 1;
}

INLINE Term spin_95(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _input_1 = r0;
  WL_SPIN
    o[0] = _input_1;
  break;
  }
  return 1;
}

INLINE Term spin_96(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  WL_SPIN
    o[0] = 0;
    o[1] = _r_0;
    o[2] = _r_1;
    o[3] = _r_2;
    o[4] = _r_3;
  break;
  }
  return 1;
}

INLINE Term spin_97(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_4 = r0;
  Term _r_5 = r1;
  Term _r_6 = r2;
  Term _r_7 = r3;
  WL_SPIN
    o[0] = 1;
    o[1] = _r_4;
    o[2] = _r_5;
    o[3] = _r_6;
    o[4] = _r_7;
  break;
  }
  return 1;
}

INLINE Term spin_98(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _state_4 = r0;
  u32 _state_5 = r1;
  Term _state_6 = r2;
  Term _state_7 = r3;
  WL_SPIN
    if (_state_4 == 0) {
      term_sink(e, _state_7);
      o[0] = term_pak(CID_Unit, 0);
    } else if (_state_4 == 1) {
      term_sink(e, _state_6);
      term_sink(e, _state_7);
      o[0] = term_pak(CID_Unit, 0);
    } else {
      o[0] = term_pak(CID_Unit, 0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_99(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _reply_0 = r0;
  WL_SPIN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _reply_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
    o[0] = term_ctr(CID_Con, _nd_0);
  break;
  }
  return 1;
}

INLINE Term spin_100(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _code_0 = r0;
  Term _msg_0 = r1;
  Term _k_0 = r2;
  WL_SPIN
    term_sink(e, _k_0);
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = _code_0;
    e.mem[_nd_0 + 1] = _msg_0;
    o[0] = term_ctr(CID_Halt, _nd_0);
  break;
  }
  return 1;
}

// Work
// ====

// A host self-jump is a tail call: as a loop, clang hoists constants badly.
#if !DEVICE
#undef  WL_SPIN
#undef  WL_SPUN
#undef  WL_AGAIN
#define WL_SPIN
#define WL_SPUN
#define WL_AGAIN    WL_JMP

typedef Term (PRESERVE(preserve_none) *WlFn)(WL_SIG);
#define WL_X(F) WL_FN WL_##F(WL_SIG);
WL_TABLE WL_X(FID_ENTER)
#undef WL_X
#define WL_X(F) WL_##F,
static const WlFn wl_tab[] = { WL_TABLE };
#undef WL_X
FAR Term work_loop(Env e, DEV Term* sp, Term t, u32 seq);
#endif

// A full lane moves the words below its def's to the heap, under an exit
// frame that moves them back (#1393).
FAR DEV Term* lane_spill(Env e, DEV Term* sp, u32 n, u32 d) {
  DEV Term* lo = e.alc + (STAK_OFF - ALC_OFF);
  u64 k = (sp - lo) / CUBE - d;
  if (d + n + 3 > STAK_LEN) {
    return 0;
  }
  u64 b = heap_alloc(e, cls_fit(STAK_LEN));
  for (u64 i = 0; i < k + d; i += 1) {
    e.mem[b + i] = lo[i * CUBE];
  }
  sp = lo;
  STK(0) = term_tsk(FID_EXIT, b);
  STK(1) = k;
  STK(2) = FID_EXIT;
  WL_PUSHN(3);
  WL_ARGS(b + k, d)
  return sp;
}

static Term work_loop(Env e, DEV Term* sp, Term t, u32 seq) {
  WL_BANK
  u32 rn = 0;
  r0 = t;
#if DEVICE
  u32 fid   = FID_ENTER;
  u32 wpoll = 0;
  WL_SPIN
  switch (fid) {
#else
  return WL_FID_ENTER(WL_ALL);
}
#endif

// Segments
// ========

// A task enters through its words: a continuation's results ride r0..
// and its parameters the stack; any other segment's parameters ride r0..

#if !DEVICE
  WL_CASE(FID_String_starts_with_go)
    Term _p_0 = r0;
    Term _s_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_p_0) == CID_SNil) {
      term_sink(e, _s_0);
      r0 = 1;
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _p_0);
      u32 _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      if (term_aux(_s_0) == CID_SNil) {
        r0 = 0;
        WL_RETN(1);
      } else {
        Term _fb_0[2];
        u64 _sp_1 = ctr_take(e, _s_0, 2, _fb_0);
        u32 _f_2 = _fb_0[0];
        Term _f_3 = _fb_0[1];
        u32 _v_0 = 0;
        Term _o_0[1];
        if (spin_5(e, _o_0, _f_2, _f_0) == 0) {
          return 0;
        }
        _v_0 = (u32)_o_0[0];
        if (_v_0 == 0) {
          term_sink(e, _f_3);
          spare_free(e, cls_fit(2), _sp_1);
          r0 = 0;
          WL_RETN(1);
        } else {
          spare_free(e, cls_fit(2), _sp_1);
          r0 = _f_1;
          r1 = _f_3;
          _p_0 = r0;
          _s_0 = r1;
          WL_AGAIN(FID_String_starts_with_go);
        }
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_String_starts_with)
    Term _s_0 = r0;
    Term _p_0 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_String_starts_with_go)) {
      u64 _t_0 = task_node(e, FID_String_starts_with_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _p_0;
      e.mem[_t_0 + 1] = _s_0;
      return term_tsk(FID_String_starts_with_go, _t_0);
    }
    r0 = _p_0;
    r1 = _s_0;
    WL_JMP(FID_String_starts_with_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_val)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_val_k12;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_val_k12, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_val_k12, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_val_k12)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_cvar_get_val_k13;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_cvar_get_val_k13, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_cvar_get_val_k13, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 1) {
        u32 _v_0 = 0;
        u32 _v_1 = 0;
        Term _v_2 = 0;
        Term _o_1[3];
        if (spin_1(e, _o_1, _h_2) == 0) {
          return 0;
        }
        _v_0 = (u32)_o_1[0];
        _v_1 = (u32)_o_1[1];
        _v_2 = _o_1[2];
        Term _o_2[4];
        if (spin_4(e, _o_2, _v_0, _v_1, _v_2) == 0) {
          return 0;
        }
        r0 = (u32)_o_2[0];
        r1 = (u32)_o_2[1];
        r2 = _o_2[2];
        r3 = _o_2[3];
        WL_RETN(4);
      } else {
        Term _x_0 = (_h_1 - 2);
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_val_k13)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_0(e, _o_0, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_String_contains)
    Term _s_0 = r0;
    Term _p_0 = r1;
    WL_OPEN
    if (term_aux(_s_0) == CID_SNil) {
      Term _o_0[1];
      if (spin_6(e, _o_0, _p_0) == 0) {
        return 0;
      }
      r0 = (u32)_o_0[0];
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_1 = ctr_take(e, _s_0, 2, _fb_0);
      u32 _f_2 = _fb_0[0];
      Term _f_3 = _fb_0[1];
      _f_3 = term_keep(e, _f_3, 1);
      u64 _nd_0 = _sp_1 >= HEAP_OFF ? _sp_1 : heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _f_2);
      e.mem[_nd_0 + 1] = rfc_seal(e, _f_3);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_3;
        STK(1) = _p_0;
        STK(2) = FID_String_contains_k16;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_String_contains_k16, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_3;
        e.mem[_t_0 + 1] = _p_0;
        WL_CONT = term_tsk(FID_String_contains_k16, _t_0);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_String_starts_with)) {
        u64 _t_1 = task_node(e, FID_String_starts_with, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = term_ctr(CID_SCon, _nd_0);
        e.mem[_t_1 + 1] = _p_0;
        return term_tsk(FID_String_starts_with, _t_1);
      }
      r0 = term_ctr(CID_SCon, _nd_0);
      r1 = _p_0;
      WL_JMP(FID_String_starts_with);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_String_contains_k16)
    WL_POPN(2);
    Term _f_4 = STK(0);
    Term _p_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (_h_0 == 0) {
      if (!DEVICE && !seq && fid_nofk(FID_String_contains)) {
        u64 _t_2 = task_node(e, FID_String_contains, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = _f_4;
        e.mem[_t_2 + 1] = _p_1;
        return term_tsk(FID_String_contains, _t_2);
      }
      r0 = _f_4;
      r1 = _p_1;
      WL_JMP(FID_String_contains);
    } else {
      term_sink(e, _f_4);
      r0 = 1;
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_matched_at)
    Term _ps_0 = r0;
    Term _u_0 = r1;
    WL_OPEN
    if (term_aux(_ps_0) == CID_Nil) {
      term_sink(e, _u_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _ps_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      if (!DEVICE && !seq && fid_nofk(FID_String_contains)) {
        u64 _t_0 = task_node(e, FID_String_contains, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _u_0;
        e.mem[_t_0 + 1] = _f_0;
        return term_tsk(FID_String_contains, _t_0);
      }
      r0 = _u_0;
      r1 = _f_0;
      WL_JMP(FID_String_contains);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_matched_go)
    Term _ps_0 = r0;
    Term _u_0 = r1;
    u32 _hit_0 = r2;
    WL_OPEN
    if (term_aux(_ps_0) == CID_Nil) {
      term_sink(e, _u_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ps_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      term_sink(e, _f_0);
      if (_hit_0 == 1) {
        term_sink(e, _f_1);
        term_sink(e, _u_0);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 1;
        WL_RETN(1);
      } else {
        _u_0 = term_keep(e, _u_0, 1);
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _f_1;
          STK(1) = _u_0;
          STK(2) = FID_child_env_matched_go_k26;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_child_env_matched_go_k26, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_1;
          e.mem[_t_0 + 1] = _u_0;
          WL_CONT = term_tsk(FID_child_env_matched_go_k26, _t_0);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_child_env_matched_at)) {
          u64 _t_1 = task_node(e, FID_child_env_matched_at, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _f_1;
          e.mem[_t_1 + 1] = _u_0;
          return term_tsk(FID_child_env_matched_at, _t_1);
        }
        r0 = _f_1;
        r1 = _u_0;
        WL_JMP(FID_child_env_matched_at);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_matched_go_k26)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _u_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_child_env_matched_go)) {
      u64 _t_2 = task_node(e, FID_child_env_matched_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _f_2;
      e.mem[_t_2 + 1] = _u_1;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_child_env_matched_go, _t_2);
    }
    r0 = _f_2;
    r1 = _u_1;
    r2 = _h_0;
    WL_JMP(FID_child_env_matched_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_matched)
    Term _ps_0 = r0;
    Term _u_0 = r1;
    WL_OPEN
    _u_0 = term_keep(e, _u_0, 1);
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _ps_0;
      STK(1) = _u_0;
      STK(2) = FID_child_env_matched_k47;
      WL_PUSHN(3);
    } else {
      u64 _t_0 = task_node(e, FID_child_env_matched_k47, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _ps_0;
      e.mem[_t_0 + 1] = _u_0;
      WL_CONT = term_tsk(FID_child_env_matched_k47, _t_0);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_child_env_matched_at)) {
      u64 _t_1 = task_node(e, FID_child_env_matched_at, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _ps_0;
      e.mem[_t_1 + 1] = _u_0;
      return term_tsk(FID_child_env_matched_at, _t_1);
    }
    r0 = _ps_0;
    r1 = _u_0;
    WL_JMP(FID_child_env_matched_at);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_matched_k47)
    WL_POPN(2);
    Term _ps_1 = STK(0);
    Term _u_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_child_env_matched_go)) {
      u64 _t_2 = task_node(e, FID_child_env_matched_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _ps_1;
      e.mem[_t_2 + 1] = _u_1;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_child_env_matched_go, _t_2);
    }
    r0 = _ps_1;
    r1 = _u_1;
    r2 = _h_0;
    WL_JMP(FID_child_env_matched_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_7)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_0);
        r2 = _cur_2;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = FID_wire_get_list_go_7_k69;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_7_k69, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          WL_CONT = term_tsk(FID_wire_get_list_go_7_k69, _t_0);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_2;
          return term_tsk(FID_wire_get_nat, _t_1);
        }
        r0 = _cur_2;
        WL_JMP(FID_wire_get_nat);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_7_k69)
    WL_POPN(2);
    Term _m_1 = STK(0);
    Term _cur_3 = STK(1);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _cur_3;
      STK(1) = FID_wire_get_list_go_7_k70;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_7_k70, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_3;
      WL_CONT = term_tsk(FID_wire_get_list_go_7_k70, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_7)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_7, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      return term_tsk(FID_wire_get_list_go_7, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    WL_JMP(FID_wire_get_list_go_7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_7_k70)
    WL_POPN(1);
    Term _cur_4 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_36(e, _o_0, _cur_4, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_7)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      r1 = _rest_0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_wire_put_list_go_7_k72;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_7_k72, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_put_list_go_7_k72, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_7);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_7_k72)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_37(e, _o_1, _f_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_str_go)
    Term _a_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_a_0) == CID_SNil) {
      r0 = 0;
      r1 = _rest_0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _a_0, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_wire_put_str_go_k74;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_str_go_k74, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_put_str_go_k74, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _a_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_str_go);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_str_go_k74)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_38(e, _o_0, _f_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    r1 = _o_0[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_named)
    Term _n_0 = r0;
    Term _xs_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      term_sink(e, _n_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      _n_0 = term_keep(e, _n_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _n_0;
        STK(1) = _f_2;
        STK(2) = _f_3;
        STK(3) = FID_child_env_named_k80;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_child_env_named_k80, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _n_0;
        e.mem[_t_0 + 1] = _f_2;
        e.mem[_t_0 + 2] = _f_3;
        WL_CONT = term_tsk(FID_child_env_named_k80, _t_0);
        WL_IDX = 3;
      }
      r0 = _n_0;
      r1 = _f_1;
      _n_0 = r0;
      _xs_0 = r1;
      WL_AGAIN(FID_child_env_named);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_named_k80)
    WL_POPN(3);
    Term _n_1 = STK(0);
    Term _f_4 = STK(1);
    Term _f_5 = STK(2);
    u32 _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _v_1 = 0;
    Term _o_0[1];
    if (spin_40(e, _o_0, _f_4, _f_5) == 0) {
      return 0;
    }
    _v_1 = _o_0[0];
    Term _o_1[1];
    if (spin_21(e, _o_1, _v_1, _n_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    r0 = ((_v_0) | (_h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_up)
    Term _s_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_s_0) == CID_SNil) {
      r0 = term_pak(CID_SNil, 0);
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _s_0);
      u32 _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_child_env_up_k86;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_child_env_up_k86, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_child_env_up_k86, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _s_0 = r0;
      WL_AGAIN(FID_child_env_up);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_up_k86)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_2[1];
    if (spin_42(e, _o_2, _f_2) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_2[0];
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_SCon, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_put_var)
    Term _v_0 = r0;
    Term _v_1 = r1;
    Term _rest_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _v_0;
      STK(1) = FID_ffi_child_env_put_var_k88;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_env_put_var_k88, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _v_0;
      WL_CONT = term_tsk(FID_ffi_child_env_put_var_k88, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_str)) {
      u64 _t_1 = task_node(e, FID_wire_put_str, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _v_1;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_str, _t_1);
    }
    r0 = _v_1;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_str);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_put_var_k88)
    WL_POPN(1);
    Term _v_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_str)) {
      u64 _t_2 = task_node(e, FID_wire_put_str, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _v_2;
      e.mem[_t_2 + 1] = _h_0;
      return term_tsk(FID_wire_put_str, _t_2);
    }
    r0 = _v_2;
    r1 = _h_0;
    WL_JMP(FID_wire_put_str);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_layer)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_director_get_layer_k90;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_director_get_layer_k90, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_director_get_layer_k90, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_layer_k90)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_director_get_layer_k91;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_director_get_layer_k91, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_director_get_layer_k91, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_nat, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_nat);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_layer_k91)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_30(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_5)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    Term _cur_3 = r4;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_0));
        e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_1);
        r2 = _cur_3;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = _cur_2;
          STK(3) = FID_wire_get_list_go_5_k93;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_5_k93, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          WL_CONT = term_tsk(FID_wire_get_list_go_5_k93, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_layer)) {
          u64 _t_1 = task_node(e, FID_ffi_director_get_layer, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_3;
          return term_tsk(FID_ffi_director_get_layer, _t_1);
        }
        r0 = _cur_3;
        WL_JMP(FID_ffi_director_get_layer);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_5_k93)
    WL_POPN(3);
    Term _m_1 = STK(0);
    Term _cur_4 = STK(1);
    Term _cur_5 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _cur_4;
      STK(1) = _cur_5;
      STK(2) = FID_wire_get_list_go_5_k94;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_5_k94, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_4;
      e.mem[_t_2 + 1] = _cur_5;
      WL_CONT = term_tsk(FID_wire_get_list_go_5_k94, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_5)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_5, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      return term_tsk(FID_wire_get_list_go_5, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    WL_JMP(FID_wire_get_list_go_5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_5_k94)
    WL_POPN(2);
    Term _cur_6 = STK(0);
    Term _cur_7 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_43(e, _o_0, _cur_6, _cur_7, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide_go)
    Term _s_0 = r0;
    Term _vs_0 = r1;
    u32 _room_0 = r2;
    u32 _stay_0 = r3;
    WL_OPEN
    WL_SPIN
    if (term_aux(_s_0) == CID_Nil) {
      r0 = 1;
      r1 = term_pak(CID_Nil, 0);
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      if (term_aux(_vs_0) == CID_Nil) {
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _f_2;
          STK(1) = _f_3;
          STK(2) = FID_director_decide_go_k100;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_director_decide_go_k100, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_2;
          e.mem[_t_0 + 1] = _f_3;
          WL_CONT = term_tsk(FID_director_decide_go_k100, _t_0);
          WL_IDX = 2;
        }
        r0 = _f_1;
        r1 = term_pak(CID_Nil, 0);
        r2 = _room_0;
        r3 = _stay_0;
        _s_0 = r0;
        _vs_0 = r1;
        _room_0 = r2;
        _stay_0 = r3;
        WL_AGAIN(FID_director_decide_go);
      } else {
        u64 _sp_2 = term_peek(e.mem, _vs_0);
        Term _f_6 = e.mem[_sp_2 + 0];
        Term _f_7 = e.mem[_sp_2 + 1];
        u32 _o_1 = 0;
        Term _o_2 = 0;
        Term _o_3 = 0;
        if (term_aux(_f_6) == CID_director_Defer) {
          _o_1 = 0;
        } else if (term_aux(_f_6) == CID_director_Again) {
          _o_1 = 1;
        } else if (term_aux(_f_6) == CID_director_Yield) {
          _o_1 = 2;
        } else if (term_aux(_f_6) == CID_director_Stack) {
          _o_1 = 3;
          u64 _sp_3 = term_peek(e.mem, _f_6);
          Term _f_8 = e.mem[_sp_3 + 0];
          Term _f_9 = e.mem[_sp_3 + 1];
          _o_2 = _f_8;
          _o_3 = _f_9;
        } else if (term_aux(_f_6) == CID_director_Leave) {
          _o_1 = 4;
        } else if (term_aux(_f_6) == CID_director_Abort) {
          _o_1 = 5;
        } else {
          _o_1 = 6;
        }
        if (_o_1 == 0) {
          spare_free(e, cls_fit(2), _sp_0);
          if (seq) {
            WL_ROOM(3, 0);
            STK(0) = _f_2;
            STK(1) = _f_3;
            STK(2) = FID_director_decide_go_k101;
            WL_PUSHN(3);
          } else {
            u64 _t_1 = task_node(e, FID_director_decide_go_k101, WL_CONT, WL_IDX, 1);
            e.mem[_t_1 + 0] = _f_2;
            e.mem[_t_1 + 1] = _f_3;
            WL_CONT = term_tsk(FID_director_decide_go_k101, _t_1);
            WL_IDX = 2;
          }
          r0 = _f_1;
          r1 = _f_7;
          r2 = _room_0;
          r3 = _stay_0;
          _s_0 = r0;
          _vs_0 = r1;
          _room_0 = r2;
          _stay_0 = r3;
          WL_AGAIN(FID_director_decide_go);
        } else if (_o_1 == 1) {
          Term _o_5[2];
          if (spin_44(e, _o_5, _f_2, _f_3, _f_1) == 0) {
            return 0;
          }
          spare_free(e, cls_fit(2), _sp_0);
          r0 = (u32)_o_5[0];
          r1 = _o_5[1];
          WL_RETN(2);
        } else if (_o_1 == 2) {
          u64 _nd_4 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
          e.mem[_nd_4 + 0] = rfc_seal(e, _f_2);
          e.mem[_nd_4 + 1] = rfc_seal(e, _f_3);
          u64 _nd_5 = heap_alloc(e, cls_fit(2));
          e.mem[_nd_5 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_4));
          e.mem[_nd_5 + 1] = rfc_seal(e, _f_1);
          r0 = 1;
          r1 = term_ctr(CID_Con, _nd_5);
          WL_RETN(2);
        } else if (_o_1 == 3) {
          Term _o_7[2];
          if (spin_45(e, _o_7, _f_2, _f_3, _o_2, _o_3, _f_1, _room_0) == 0) {
            return 0;
          }
          spare_free(e, cls_fit(2), _sp_0);
          r0 = (u32)_o_7[0];
          r1 = _o_7[1];
          WL_RETN(2);
        } else if (_o_1 == 4) {
          spare_free(e, cls_fit(2), _sp_0);
          r0 = _f_1;
          r1 = _f_7;
          r2 = _room_0;
          r3 = _stay_0;
          _s_0 = r0;
          _vs_0 = r1;
          _room_0 = r2;
          _stay_0 = r3;
          WL_AGAIN(FID_director_decide_go);
        } else if (_o_1 == 5) {
          u64 _nd_8 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
          e.mem[_nd_8 + 0] = rfc_seal(e, _f_2);
          e.mem[_nd_8 + 1] = rfc_seal(e, _f_3);
          u64 _nd_9 = heap_alloc(e, cls_fit(2));
          e.mem[_nd_9 + 0] = rfc_seal(e, term_ctr(CID_director_Layer, _nd_8));
          e.mem[_nd_9 + 1] = rfc_seal(e, _f_1);
          r0 = 2;
          r1 = term_ctr(CID_Con, _nd_9);
          WL_RETN(2);
        } else {
          spare_free(e, cls_fit(2), _sp_0);
          if (seq) {
            WL_ROOM(4, 0);
            STK(0) = _f_2;
            STK(1) = _f_3;
            STK(2) = _stay_0;
            STK(3) = FID_director_decide_go_k102;
            WL_PUSHN(4);
          } else {
            u64 _t_2 = task_node(e, FID_director_decide_go_k102, WL_CONT, WL_IDX, 1);
            e.mem[_t_2 + 0] = _f_2;
            e.mem[_t_2 + 1] = _f_3;
            e.mem[_t_2 + 2] = _stay_0;
            WL_CONT = term_tsk(FID_director_decide_go_k102, _t_2);
            WL_IDX = 3;
          }
          r0 = _f_1;
          r1 = _f_7;
          r2 = _room_0;
          r3 = _stay_0;
          _s_0 = r0;
          _vs_0 = r1;
          _room_0 = r2;
          _stay_0 = r3;
          WL_AGAIN(FID_director_decide_go);
        }
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide_go_k100)
    WL_POPN(2);
    Term _f_4 = STK(0);
    Term _f_5 = STK(1);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_33(e, _o_0, _f_4, _f_5, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide_go_k101)
    WL_POPN(2);
    Term _f_10 = STK(0);
    Term _f_11 = STK(1);
    u32 _h_2 = r0;
    Term _h_3 = r1;
    WL_OPEN
    Term _o_4[2];
    if (spin_33(e, _o_4, _f_10, _f_11, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_4[0];
    r1 = _o_4[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide_go_k102)
    WL_POPN(3);
    Term _f_12 = STK(0);
    Term _f_13 = STK(1);
    u32 _stay_1 = STK(2);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    WL_OPEN
    Term _o_9[2];
    if (spin_46(e, _o_9, _stay_1, _f_12, _f_13, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_9[0];
    r1 = _o_9[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_cmd_k110;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_cmd_k110, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_cmd_k110, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd_k110)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_cvar_get_cmd_k111;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_cvar_get_cmd_k111, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_cvar_get_cmd_k111, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_cvar_get_cmd_k113;
          WL_PUSHN(1);
        } else {
          u64 _t_6 = task_node(e, FID_ffi_cvar_get_cmd_k113, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_cvar_get_cmd_k113, _t_6);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_7 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_7 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_7);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 2) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_cvar_get_cmd_k114;
          WL_PUSHN(1);
        } else {
          u64 _t_8 = task_node(e, FID_ffi_cvar_get_cmd_k114, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_cvar_get_cmd_k114, _t_8);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_9 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_9 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_9);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 3) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_cvar_get_cmd_k115;
          WL_PUSHN(1);
        } else {
          u64 _t_10 = task_node(e, FID_ffi_cvar_get_cmd_k115, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_cvar_get_cmd_k115, _t_10);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_11 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_11 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_11);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else {
        Term _x_0 = (_h_1 - 4);
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        WL_RETN(6);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd_k111)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_4;
        STK(1) = FID_ffi_cvar_get_cmd_k112;
        WL_PUSHN(2);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_cvar_get_cmd_k112, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_4;
        WL_CONT = term_tsk(FID_ffi_cvar_get_cmd_k112, _t_4);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_val)) {
        u64 _t_5 = task_node(e, FID_ffi_cvar_get_val, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_ffi_cvar_get_val, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_ffi_cvar_get_val);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd_k112)
    WL_POPN(1);
    Term _h_10 = STK(0);
    u32 _h_6 = r0;
    u32 _h_7 = r1;
    Term _h_8 = r2;
    Term _h_9 = r3;
    WL_OPEN
    Term _o_0[6];
    if (spin_7(e, _o_0, _h_10, _h_6, _h_7, _h_8, _h_9) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = (u32)_o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd_k113)
    u32 _h_11 = r0;
    Term _h_12 = r1;
    Term _h_13 = r2;
    WL_OPEN
    Term _o_1[6];
    if (spin_18(e, _o_1, _h_11, _h_12, _h_13) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = (u32)_o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd_k114)
    u32 _h_14 = r0;
    Term _h_15 = r1;
    Term _h_16 = r2;
    WL_OPEN
    Term _o_2[6];
    if (spin_19(e, _o_2, _h_14, _h_15, _h_16) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    r3 = (u32)_o_2[3];
    r4 = _o_2[4];
    r5 = _o_2[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmd_k115)
    u32 _h_17 = r0;
    Term _h_18 = r1;
    Term _h_19 = r2;
    WL_OPEN
    Term _o_3[6];
    if (spin_20(e, _o_3, _h_17, _h_18, _h_19) == 0) {
      return 0;
    }
    r0 = (u32)_o_3[0];
    r1 = (u32)_o_3[1];
    r2 = _o_3[2];
    r3 = (u32)_o_3[3];
    r4 = _o_3[4];
    r5 = _o_3[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_2)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    u32 _cur_1 = r2;
    Term _cur_2 = r3;
    u32 _cur_3 = r4;
    Term _cur_4 = r5;
    Term _cur_5 = r6;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        Term _b_0 = 0;
        if (_cur_1 == 0) {
          u64 _nd_0 = heap_alloc(e, cls_fit(3));
          e.mem[_nd_0 + 0] = rfc_seal(e, _cur_2);
          e.mem[_nd_0 + 1] = rfc_seal(e, _cur_3);
          e.mem[_nd_0 + 2] = rfc_seal(e, _cur_4);
          _b_0 = term_ctr(CID_cvar_CSet, _nd_0);
        } else if (_cur_1 == 1) {
          u64 _nd_1 = heap_alloc(e, cls_fit(1));
          e.mem[_nd_1 + 0] = rfc_seal(e, _cur_2);
          _b_0 = term_ctr(CID_cvar_CToggle, _nd_1);
        } else if (_cur_1 == 2) {
          u64 _nd_2 = heap_alloc(e, cls_fit(1));
          e.mem[_nd_2 + 0] = rfc_seal(e, _cur_2);
          _b_0 = term_ctr(CID_cvar_CRun, _nd_2);
        } else {
          u64 _nd_3 = heap_alloc(e, cls_fit(1));
          e.mem[_nd_3 + 0] = rfc_seal(e, _cur_2);
          _b_0 = term_ctr(CID_cvar_CGone, _nd_3);
        }
        u64 _nd_4 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_4 + 0] = rfc_seal(e, _b_0);
        e.mem[_nd_4 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_4);
        r2 = _cur_5;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(6, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = _cur_2;
          STK(3) = _cur_3;
          STK(4) = _cur_4;
          STK(5) = FID_wire_get_list_go_2_k117;
          WL_PUSHN(6);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_2_k117, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          e.mem[_t_0 + 3] = _cur_3;
          e.mem[_t_0 + 4] = _cur_4;
          WL_CONT = term_tsk(FID_wire_get_list_go_2_k117, _t_0);
          WL_IDX = 5;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_cmd)) {
          u64 _t_1 = task_node(e, FID_ffi_cvar_get_cmd, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_5;
          return term_tsk(FID_ffi_cvar_get_cmd, _t_1);
        }
        r0 = _cur_5;
        WL_JMP(FID_ffi_cvar_get_cmd);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_2_k117)
    WL_POPN(5);
    Term _m_1 = STK(0);
    u32 _cur_6 = STK(1);
    Term _cur_7 = STK(2);
    u32 _cur_8 = STK(3);
    Term _cur_9 = STK(4);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    u32 _h_3 = r3;
    Term _h_4 = r4;
    Term _h_5 = r5;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _cur_6;
      STK(1) = _cur_7;
      STK(2) = _cur_8;
      STK(3) = _cur_9;
      STK(4) = FID_wire_get_list_go_2_k118;
      WL_PUSHN(5);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_2_k118, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_6;
      e.mem[_t_2 + 1] = _cur_7;
      e.mem[_t_2 + 2] = _cur_8;
      e.mem[_t_2 + 3] = _cur_9;
      WL_CONT = term_tsk(FID_wire_get_list_go_2_k118, _t_2);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_2)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_2, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      e.mem[_t_3 + 5] = _h_4;
      e.mem[_t_3 + 6] = _h_5;
      return term_tsk(FID_wire_get_list_go_2, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    r5 = _h_4;
    r6 = _h_5;
    WL_JMP(FID_wire_get_list_go_2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_2_k118)
    WL_POPN(4);
    u32 _cur_10 = STK(0);
    Term _cur_11 = STK(1);
    u32 _cur_12 = STK(2);
    Term _cur_13 = STK(3);
    u32 _h_6 = r0;
    Term _h_7 = r1;
    Term _h_8 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_51(e, _o_0, _cur_10, _cur_11, _cur_12, _cur_13, _h_6, _h_7, _h_8) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_7)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_7_k122;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_7_k122, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_7_k122, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_7)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_7, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _xs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_7, _t_1);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_7_k122)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[1];
    if (spin_52(e, _o_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_str)
    Term _a_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_str_k124;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_str_k124, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_str_k124, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_str_go)) {
      u64 _t_1 = task_node(e, FID_wire_put_str_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _a_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_str_go, _t_1);
    }
    r0 = _a_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_str_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_str_k124)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[1];
    if (spin_53(e, _o_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_take)
    Term _n_0 = r0;
    Term _s_0 = r1;
    WL_OPEN
    WL_SPIN
    if (_n_0 == 0) {
      r0 = 0;
      r1 = term_pak(CID_SNil, 0);
      r2 = _s_0;
      WL_RETN(3);
    } else {
      Term _m_0 = (_n_0 - 1);
      if (term_aux(_s_0) == CID_SNil) {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      } else {
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _s_0, 2, _fb_0);
        u32 _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _f_0;
          STK(1) = FID_wire_take_k128;
          WL_PUSHN(2);
        } else {
          u64 _t_0 = task_node(e, FID_wire_take_k128, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_0;
          WL_CONT = term_tsk(FID_wire_take_k128, _t_0);
          WL_IDX = 1;
        }
        r0 = _m_0;
        r1 = _f_1;
        _n_0 = r0;
        _s_0 = r1;
        WL_AGAIN(FID_wire_take);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_take_k128)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_54(e, _o_0, _f_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_var)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_env_get_var_k130;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_env_get_var_k130, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_env_get_var_k130, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
      u64 _t_1 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_str, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_str);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_var_k130)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_child_env_get_var_k131;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_child_env_get_var_k131, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_child_env_get_var_k131, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
        u64 _t_3 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_str, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_str);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_var_k131)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_39(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_0)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    Term _cur_3 = r4;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_child_env_Var, _nd_0));
        e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_1);
        r2 = _cur_3;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = _cur_2;
          STK(3) = FID_wire_get_list_go_0_k133;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_0_k133, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          WL_CONT = term_tsk(FID_wire_get_list_go_0_k133, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_env_get_var)) {
          u64 _t_1 = task_node(e, FID_ffi_child_env_get_var, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_3;
          return term_tsk(FID_ffi_child_env_get_var, _t_1);
        }
        r0 = _cur_3;
        WL_JMP(FID_ffi_child_env_get_var);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_0_k133)
    WL_POPN(3);
    Term _m_1 = STK(0);
    Term _cur_4 = STK(1);
    Term _cur_5 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _cur_4;
      STK(1) = _cur_5;
      STK(2) = FID_wire_get_list_go_0_k134;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_0_k134, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_4;
      e.mem[_t_2 + 1] = _cur_5;
      WL_CONT = term_tsk(FID_wire_get_list_go_0_k134, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_0)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      return term_tsk(FID_wire_get_list_go_0, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    WL_JMP(FID_wire_get_list_go_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_0_k134)
    WL_POPN(2);
    Term _cur_6 = STK(0);
    Term _cur_7 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_55(e, _o_0, _cur_6, _cur_7, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_under)
    Term _base_0 = r0;
    Term _over_0 = r1;
    WL_OPEN
    if (term_aux(_base_0) == CID_Nil) {
      term_sink(e, _over_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _base_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      Term _v_0 = 0;
      _f_2 = term_keep(e, _f_2, 1);
      _f_3 = term_keep(e, _f_3, 1);
      Term _o_0[1];
      if (spin_40(e, _o_0, _f_2, _f_3) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      _over_0 = term_keep(e, _over_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_1;
        STK(3) = _over_0;
        STK(4) = FID_child_env_under_k136;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_child_env_under_k136, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_1;
        e.mem[_t_0 + 3] = _over_0;
        WL_CONT = term_tsk(FID_child_env_under_k136, _t_0);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_child_env_named)) {
        u64 _t_1 = task_node(e, FID_child_env_named, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _v_0;
        e.mem[_t_1 + 1] = _over_0;
        return term_tsk(FID_child_env_named, _t_1);
      }
      r0 = _v_0;
      r1 = _over_0;
      WL_JMP(FID_child_env_named);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_under_k136)
    WL_POPN(4);
    Term _f_4 = STK(0);
    Term _f_5 = STK(1);
    Term _f_6 = STK(2);
    Term _over_1 = STK(3);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _f_4;
      STK(1) = _f_5;
      STK(2) = _h_0;
      STK(3) = FID_child_env_under_k137;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_child_env_under_k137, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _f_4;
      e.mem[_t_2 + 1] = _f_5;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_child_env_under_k137, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_child_env_under)) {
      u64 _t_3 = task_node(e, FID_child_env_under, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_6;
      e.mem[_t_3 + 1] = _over_1;
      return term_tsk(FID_child_env_under, _t_3);
    }
    r0 = _f_6;
    r1 = _over_1;
    WL_JMP(FID_child_env_under);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_under_k137)
    WL_POPN(3);
    Term _f_7 = STK(0);
    Term _f_8 = STK(1);
    u32 _h_2 = STK(2);
    Term _h_1 = r0;
    WL_OPEN
    Term _o_1[1];
    if (spin_56(e, _o_1, _h_2, _f_7, _f_8, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_List_append)
    Term _xs_0 = r0;
    Term _ys_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = _ys_0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_List_append_k139;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_List_append_k139, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_List_append_k139, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      r1 = _ys_0;
      _xs_0 = r0;
      _ys_0 = r1;
      WL_AGAIN(FID_List_append);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_List_append_k139)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _f_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_passes)
    Term _reg_0 = r0;
    Term _keep_0 = r1;
    Term _n_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _reg_0;
      STK(1) = _keep_0;
      STK(2) = _n_0;
      STK(3) = FID_child_env_passes_k142;
      WL_PUSHN(4);
    } else {
      u64 _t_0 = task_node(e, FID_child_env_passes_k142, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _reg_0;
      e.mem[_t_0 + 1] = _keep_0;
      e.mem[_t_0 + 2] = _n_0;
      WL_CONT = term_tsk(FID_child_env_passes_k142, _t_0);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_child_env_up)) {
      u64 _t_1 = task_node(e, FID_child_env_up, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _n_0;
      return term_tsk(FID_child_env_up, _t_1);
    }
    r0 = _n_0;
    WL_JMP(FID_child_env_up);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_passes_k142)
    WL_POPN(3);
    Term _reg_1 = STK(0);
    Term _keep_1 = STK(1);
    Term _n_1 = STK(2);
    Term _u_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    _u_0 = term_keep(e, _u_0, 1);
    Term _o_0[1];
    if (spin_26(e, _o_0, _reg_1, _u_0) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    if (_v_0 == 1) {
      term_sink(e, _u_0);
      term_sink(e, _keep_1);
      term_sink(e, _n_1);
      r0 = 0;
      WL_RETN(1);
    } else {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _keep_1;
        STK(1) = _n_1;
        STK(2) = FID_child_env_passes_k143;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_child_env_passes_k143, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _keep_1;
        e.mem[_t_2 + 1] = _n_1;
        WL_CONT = term_tsk(FID_child_env_passes_k143, _t_2);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_child_env_matched)) {
        u64 _t_3 = task_node(e, FID_child_env_matched, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = term_ctr(CID_Con, STAT_OFF + 152);
        e.mem[_t_3 + 1] = _u_0;
        return term_tsk(FID_child_env_matched, _t_3);
      }
      r0 = term_ctr(CID_Con, STAT_OFF + 152);
      r1 = _u_0;
      WL_JMP(FID_child_env_matched);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_passes_k143)
    WL_POPN(2);
    Term _keep_2 = STK(0);
    Term _n_2 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    Term _o_1[1];
    if (spin_41(e, _o_1, _h_0, _keep_2, _n_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_end)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_director_get_end_k150;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_director_get_end_k150, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_director_get_end_k150, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_end_k150)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = 0;
        r2 = 0;
        r3 = _h_2;
        WL_RETN(4);
      } else if (_h_1 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_director_get_end_k151;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_director_get_end_k151, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_director_get_end_k151, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else {
        Term _x_0 = (_h_1 - 2);
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_end_k151)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_31(e, _o_0, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = (u32)_o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_verdict)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_director_get_verdict_k154;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_director_get_verdict_k154, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_director_get_verdict_k154, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_verdict_k154)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_h_1 == 1) {
        r0 = 0;
        r1 = 1;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_h_1 == 2) {
        r0 = 0;
        r1 = 2;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_h_1 == 3) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_director_get_verdict_k155;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_director_get_verdict_k155, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_director_get_verdict_k155, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_layer)) {
          u64 _t_3 = task_node(e, FID_ffi_director_get_layer, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_director_get_layer, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_director_get_layer);
      } else if (_h_1 == 4) {
        r0 = 0;
        r1 = 4;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_h_1 == 5) {
        r0 = 0;
        r1 = 5;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_h_1 == 6) {
        r0 = 0;
        r1 = 6;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else {
        Term _x_0 = (_h_1 - 7);
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        WL_RETN(5);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_verdict_k155)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_32(e, _o_0, _h_3, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_6)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    u32 _cur_1 = r2;
    Term _cur_2 = r3;
    Term _cur_3 = r4;
    Term _cur_4 = r5;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        Term _b_0 = 0;
        if (_cur_1 == 0) {
          _b_0 = term_pak(CID_director_Defer, 0);
        } else if (_cur_1 == 1) {
          _b_0 = term_pak(CID_director_Again, 0);
        } else if (_cur_1 == 2) {
          _b_0 = term_pak(CID_director_Yield, 0);
        } else if (_cur_1 == 3) {
          u64 _nd_0 = heap_alloc(e, cls_fit(2));
          e.mem[_nd_0 + 0] = rfc_seal(e, _cur_2);
          e.mem[_nd_0 + 1] = rfc_seal(e, _cur_3);
          _b_0 = term_ctr(CID_director_Stack, _nd_0);
        } else if (_cur_1 == 4) {
          _b_0 = term_pak(CID_director_Leave, 0);
        } else if (_cur_1 == 5) {
          _b_0 = term_pak(CID_director_Abort, 0);
        } else {
          _b_0 = term_pak(CID_director_Lead, 0);
        }
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, _b_0);
        e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_1);
        r2 = _cur_4;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(5, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = _cur_2;
          STK(3) = _cur_3;
          STK(4) = FID_wire_get_list_go_6_k157;
          WL_PUSHN(5);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_6_k157, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          e.mem[_t_0 + 3] = _cur_3;
          WL_CONT = term_tsk(FID_wire_get_list_go_6_k157, _t_0);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_verdict)) {
          u64 _t_1 = task_node(e, FID_ffi_director_get_verdict, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_4;
          return term_tsk(FID_ffi_director_get_verdict, _t_1);
        }
        r0 = _cur_4;
        WL_JMP(FID_ffi_director_get_verdict);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_6_k157)
    WL_POPN(4);
    Term _m_1 = STK(0);
    u32 _cur_5 = STK(1);
    Term _cur_6 = STK(2);
    Term _cur_7 = STK(3);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _cur_5;
      STK(1) = _cur_6;
      STK(2) = _cur_7;
      STK(3) = FID_wire_get_list_go_6_k158;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_6_k158, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_5;
      e.mem[_t_2 + 1] = _cur_6;
      e.mem[_t_2 + 2] = _cur_7;
      WL_CONT = term_tsk(FID_wire_get_list_go_6_k158, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_6)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_6, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      e.mem[_t_3 + 5] = _h_4;
      return term_tsk(FID_wire_get_list_go_6, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    r5 = _h_4;
    WL_JMP(FID_wire_get_list_go_6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_6_k158)
    WL_POPN(3);
    u32 _cur_8 = STK(0);
    Term _cur_9 = STK(1);
    Term _cur_10 = STK(2);
    u32 _h_5 = r0;
    Term _h_6 = r1;
    Term _h_7 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_57(e, _o_0, _cur_8, _cur_9, _cur_10, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide_as)
    Term _s_0 = r0;
    Term _vs_0 = r1;
    Term _cap_0 = r2;
    u32 _stay_0 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _s_0;
      STK(1) = _vs_0;
      STK(2) = _cap_0;
      STK(3) = _stay_0;
      STK(4) = FID_director_decide_as_k160;
      WL_PUSHN(5);
    } else {
      u64 _t_0 = task_node(e, FID_director_decide_as_k160, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _s_0;
      e.mem[_t_0 + 1] = _vs_0;
      e.mem[_t_0 + 2] = _cap_0;
      e.mem[_t_0 + 3] = _stay_0;
      WL_CONT = term_tsk(FID_director_decide_as_k160, _t_0);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
      u64 _t_1 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_List_length, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_List_length);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide_as_k160)
    WL_POPN(4);
    Term _s_1 = STK(0);
    Term _vs_1 = STK(1);
    Term _cap_1 = STK(2);
    u32 _stay_1 = STK(3);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_director_decide_go)) {
      u64 _t_2 = task_node(e, FID_director_decide_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _s_1;
      e.mem[_t_2 + 1] = _vs_1;
      e.mem[_t_2 + 2] = (_h_0 < _cap_1);
      e.mem[_t_2 + 3] = _stay_1;
      return term_tsk(FID_director_decide_go, _t_2);
    }
    r0 = _s_1;
    r1 = _vs_1;
    r2 = (_h_0 < _cap_1);
    r3 = _stay_1;
    WL_JMP(FID_director_decide_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_kept)
    Term _s_0 = r0;
    Term _vs_0 = r1;
    Term _cap_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _vs_0;
      STK(1) = FID_director_kept_k162;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_director_kept_k162, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _vs_0;
      WL_CONT = term_tsk(FID_director_kept_k162, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_director_decide_as)) {
      u64 _t_1 = task_node(e, FID_director_decide_as, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      e.mem[_t_1 + 1] = _vs_0;
      e.mem[_t_1 + 2] = _cap_0;
      e.mem[_t_1 + 3] = 1;
      return term_tsk(FID_director_decide_as, _t_1);
    }
    r0 = _s_0;
    r1 = _vs_0;
    r2 = _cap_0;
    r3 = 1;
    WL_JMP(FID_director_decide_as);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_kept_k162)
    WL_POPN(1);
    Term _vs_1 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    term_sink(e, _vs_1);
    Term _o_0[1];
    if (spin_58(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_5)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      r1 = _rest_0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = FID_wire_put_list_go_5_k167;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_5_k167, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        WL_CONT = term_tsk(FID_wire_put_list_go_5_k167, _t_0);
        WL_IDX = 2;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_5);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_5_k167)
    WL_POPN(2);
    Term _f_4 = STK(0);
    Term _f_5 = STK(1);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_59(e, _o_1, _f_4, _f_5, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_2)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      r1 = _rest_0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u32 _o_0 = 0;
      Term _o_1 = 0;
      u32 _o_2 = 0;
      Term _o_3 = 0;
      if (term_aux(_f_0) == CID_cvar_CSet) {
        _o_0 = 0;
        Term _fb_1[3];
        u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
        Term _f_2 = _fb_1[0];
        u32 _f_3 = _fb_1[1];
        Term _f_4 = _fb_1[2];
        spare_free(e, cls_fit(3), _sp_1);
        _o_1 = _f_2;
        _o_2 = _f_3;
        _o_3 = _f_4;
      } else if (term_aux(_f_0) == CID_cvar_CToggle) {
        _o_0 = 1;
        Term _fb_2[1];
        u64 _sp_2 = ctr_take(e, _f_0, 1, _fb_2);
        Term _f_5 = _fb_2[0];
        spare_free(e, cls_fit(1), _sp_2);
        _o_1 = _f_5;
      } else if (term_aux(_f_0) == CID_cvar_CRun) {
        _o_0 = 2;
        Term _fb_3[1];
        u64 _sp_3 = ctr_take(e, _f_0, 1, _fb_3);
        Term _f_6 = _fb_3[0];
        spare_free(e, cls_fit(1), _sp_3);
        _o_1 = _f_6;
      } else {
        _o_0 = 3;
        Term _fb_4[1];
        u64 _sp_4 = ctr_take(e, _f_0, 1, _fb_4);
        Term _f_7 = _fb_4[0];
        spare_free(e, cls_fit(1), _sp_4);
        _o_1 = _f_7;
      }
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _o_0;
        STK(1) = _o_1;
        STK(2) = _o_2;
        STK(3) = _o_3;
        STK(4) = FID_wire_put_list_go_2_k172;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_2_k172, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _o_0;
        e.mem[_t_0 + 1] = _o_1;
        e.mem[_t_0 + 2] = _o_2;
        e.mem[_t_0 + 3] = _o_3;
        WL_CONT = term_tsk(FID_wire_put_list_go_2_k172, _t_0);
        WL_IDX = 4;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_2);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_2_k172)
    WL_POPN(4);
    u32 _o_4 = STK(0);
    Term _o_5 = STK(1);
    u32 _o_6 = STK(2);
    Term _o_7 = STK(3);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_9[2];
    if (spin_61(e, _o_9, _o_4, _o_5, _o_6, _o_7, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_9[0];
    r1 = _o_9[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_value)
    Term _ds_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ds_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ds_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_wire_value_k182;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_value_k182, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_value_k182, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _ds_0 = r0;
      WL_AGAIN(FID_wire_value);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_value_k182)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _f_2 + nat_mul(e, 10ull, _h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_7)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_7_k185;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_7_k185, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_7_k185, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_7_k185)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_7_k186;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_7_k186, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_7_k186, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_7_k186)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_7)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_7, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      return term_tsk(FID_wire_get_list_go_7, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    WL_JMP(FID_wire_get_list_go_7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_merge)
    Term _base_0 = r0;
    Term _over_0 = r1;
    WL_OPEN
    _over_0 = term_keep(e, _over_0, 1);
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _over_0;
      STK(1) = FID_child_env_merge_k195;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_child_env_merge_k195, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _over_0;
      WL_CONT = term_tsk(FID_child_env_merge_k195, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_child_env_under)) {
      u64 _t_1 = task_node(e, FID_child_env_under, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _base_0;
      e.mem[_t_1 + 1] = _over_0;
      return term_tsk(FID_child_env_under, _t_1);
    }
    r0 = _base_0;
    r1 = _over_0;
    WL_JMP(FID_child_env_under);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_merge_k195)
    WL_POPN(1);
    Term _over_1 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_List_append)) {
      u64 _t_2 = task_node(e, FID_List_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _over_1;
      e.mem[_t_2 + 1] = _h_0;
      return term_tsk(FID_List_append, _t_2);
    }
    r0 = _over_1;
    r1 = _h_0;
    WL_JMP(FID_List_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_keep)
    Term _reg_0 = r0;
    Term _ks_0 = r1;
    Term _xs_0 = r2;
    WL_OPEN
    if (term_aux(_xs_0) == CID_Nil) {
      term_sink(e, _reg_0);
      term_sink(e, _ks_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      Term _v_0 = 0;
      _f_2 = term_keep(e, _f_2, 1);
      _f_3 = term_keep(e, _f_3, 1);
      Term _o_0[1];
      if (spin_40(e, _o_0, _f_2, _f_3) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      _reg_0 = term_keep(e, _reg_0, 1);
      _ks_0 = term_keep(e, _ks_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _reg_0;
        STK(1) = _ks_0;
        STK(2) = _f_2;
        STK(3) = _f_3;
        STK(4) = _f_1;
        STK(5) = FID_child_env_keep_k197;
        WL_PUSHN(6);
      } else {
        u64 _t_0 = task_node(e, FID_child_env_keep_k197, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _reg_0;
        e.mem[_t_0 + 1] = _ks_0;
        e.mem[_t_0 + 2] = _f_2;
        e.mem[_t_0 + 3] = _f_3;
        e.mem[_t_0 + 4] = _f_1;
        WL_CONT = term_tsk(FID_child_env_keep_k197, _t_0);
        WL_IDX = 5;
      }
      if (!DEVICE && !seq && fid_nofk(FID_child_env_passes)) {
        u64 _t_1 = task_node(e, FID_child_env_passes, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _reg_0;
        e.mem[_t_1 + 1] = _ks_0;
        e.mem[_t_1 + 2] = _v_0;
        return term_tsk(FID_child_env_passes, _t_1);
      }
      r0 = _reg_0;
      r1 = _ks_0;
      r2 = _v_0;
      WL_JMP(FID_child_env_passes);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_keep_k197)
    WL_POPN(5);
    Term _reg_1 = STK(0);
    Term _ks_1 = STK(1);
    Term _f_4 = STK(2);
    Term _f_5 = STK(3);
    Term _f_6 = STK(4);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _f_4;
      STK(1) = _f_5;
      STK(2) = _h_0;
      STK(3) = FID_child_env_keep_k198;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_child_env_keep_k198, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _f_4;
      e.mem[_t_2 + 1] = _f_5;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_child_env_keep_k198, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_child_env_keep)) {
      u64 _t_3 = task_node(e, FID_child_env_keep, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _reg_1;
      e.mem[_t_3 + 1] = _ks_1;
      e.mem[_t_3 + 2] = _f_6;
      return term_tsk(FID_child_env_keep, _t_3);
    }
    r0 = _reg_1;
    r1 = _ks_1;
    r2 = _f_6;
    WL_JMP(FID_child_env_keep);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_keep_k198)
    WL_POPN(3);
    Term _f_7 = STK(0);
    Term _f_8 = STK(1);
    u32 _h_2 = STK(2);
    Term _h_1 = r0;
    WL_OPEN
    Term _o_1[1];
    if (spin_66(e, _o_1, _h_2, _f_7, _f_8, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_1)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      r1 = _rest_0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = FID_wire_put_list_go_1_k200;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_1_k200, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        WL_CONT = term_tsk(FID_wire_put_list_go_1_k200, _t_0);
        WL_IDX = 2;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_1);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_1_k200)
    WL_POPN(2);
    Term _f_4 = STK(0);
    Term _f_5 = STK(1);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_wire_put_list_go_1_k201;
      WL_PUSHN(2);
    } else {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_1_k201, WL_CONT, WL_IDX, 1);
      e.mem[_t_1 + 0] = _h_0;
      WL_CONT = term_tsk(FID_wire_put_list_go_1_k201, _t_1);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_child_env_put_var)) {
      u64 _t_2 = task_node(e, FID_ffi_child_env_put_var, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _f_4;
      e.mem[_t_2 + 1] = _f_5;
      e.mem[_t_2 + 2] = _h_1;
      return term_tsk(FID_ffi_child_env_put_var, _t_2);
    }
    r0 = _f_4;
    r1 = _f_5;
    r2 = _h_1;
    WL_JMP(FID_ffi_child_env_put_var);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_1_k201)
    WL_POPN(1);
    Term _h_3 = STK(0);
    Term _h_2 = r0;
    WL_OPEN
    r0 = nat_chk(e, _h_3 + 1);
    r1 = _h_2;
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_5)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_5_k204;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_5_k204, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_5_k204, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_5_k204)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_5_k205;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_5_k205, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_5_k205, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_layer)) {
          u64 _t_3 = task_node(e, FID_ffi_director_get_layer, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_director_get_layer, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_director_get_layer);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_5_k205)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_5)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_5, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      return term_tsk(FID_wire_get_list_go_5, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    WL_JMP(FID_wire_get_list_go_5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_decide)
    Term _s_0 = r0;
    Term _vs_0 = r1;
    Term _cap_0 = r2;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_director_decide_as)) {
      u64 _t_0 = task_node(e, FID_director_decide_as, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _s_0;
      e.mem[_t_0 + 1] = _vs_0;
      e.mem[_t_0 + 2] = _cap_0;
      e.mem[_t_0 + 3] = 0;
      return term_tsk(FID_director_decide_as, _t_0);
    }
    r0 = _s_0;
    r1 = _vs_0;
    r2 = _cap_0;
    r3 = 0;
    WL_JMP(FID_director_decide_as);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_5)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_5_k217;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_5_k217, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_5_k217, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_5)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_5, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _xs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_5, _t_1);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_5_k217)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[1];
    if (spin_52(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_List_length)
    Term _xs_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _xs_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_List_length_k225;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_List_length_k225, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_List_length_k225, _t_0);
        WL_IDX = 0;
      }
      r0 = _f_1;
      _xs_0 = r0;
      WL_AGAIN(FID_List_length);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_List_length_k225)
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _h_0 + 1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cvar_expand_go)
    Term _d_0 = r0;
    Term _cs_0 = r1;
    Term _as_0 = r2;
    u32 _acc_0 = r3;
    Term _acc_1 = r4;
    WL_OPEN
    WL_SPIN
    if (_d_0 == 0) {
      if (term_aux(_cs_0) == CID_Nil) {
        term_sink(e, _as_0);
        r0 = _acc_0;
        r1 = _acc_1;
        WL_RETN(2);
      } else {
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _cs_0, 2, _fb_0);
        Term _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        u32 _o_0 = 0;
        Term _o_1 = 0;
        u32 _o_2 = 0;
        Term _o_3 = 0;
        if (term_aux(_f_0) == CID_cvar_CSet) {
          _o_0 = 0;
          Term _fb_1[3];
          u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
          Term _f_2 = _fb_1[0];
          u32 _f_3 = _fb_1[1];
          Term _f_4 = _fb_1[2];
          spare_free(e, cls_fit(3), _sp_1);
          _o_1 = _f_2;
          _o_2 = _f_3;
          _o_3 = _f_4;
        } else if (term_aux(_f_0) == CID_cvar_CToggle) {
          _o_0 = 1;
          Term _fb_2[1];
          u64 _sp_2 = ctr_take(e, _f_0, 1, _fb_2);
          Term _f_5 = _fb_2[0];
          spare_free(e, cls_fit(1), _sp_2);
          _o_1 = _f_5;
        } else if (term_aux(_f_0) == CID_cvar_CRun) {
          _o_0 = 2;
          Term _fb_3[1];
          u64 _sp_3 = ctr_take(e, _f_0, 1, _fb_3);
          Term _f_6 = _fb_3[0];
          spare_free(e, cls_fit(1), _sp_3);
          _o_1 = _f_6;
        } else {
          _o_0 = 3;
          Term _fb_4[1];
          u64 _sp_4 = ctr_take(e, _f_0, 1, _fb_4);
          Term _f_7 = _fb_4[0];
          spare_free(e, cls_fit(1), _sp_4);
          _o_1 = _f_7;
        }
        if (_o_0 == 0) {
          if (_acc_0 == 0) {
            u64 _nd_0 = heap_alloc(e, cls_fit(3));
            e.mem[_nd_0 + 0] = rfc_seal(e, _o_1);
            e.mem[_nd_0 + 1] = rfc_seal(e, _o_2);
            e.mem[_nd_0 + 2] = rfc_seal(e, _o_3);
            u64 _nd_1 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
            e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_cvar_CSet, _nd_0));
            e.mem[_nd_1 + 1] = rfc_seal(e, _acc_1);
            r0 = 0;
            r1 = _f_1;
            r2 = _as_0;
            r3 = 0;
            r4 = term_ctr(CID_Con, _nd_1);
            _d_0 = r0;
            _cs_0 = r1;
            _as_0 = r2;
            _acc_0 = r3;
            _acc_1 = r4;
            WL_AGAIN(FID_cvar_expand_go);
          } else if (_acc_0 == 1) {
            term_sink(e, _f_1);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            term_sink(e, _f_1);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        } else if (_o_0 == 1) {
          if (_acc_0 == 0) {
            u64 _nd_2 = heap_alloc(e, cls_fit(1));
            e.mem[_nd_2 + 0] = rfc_seal(e, _o_1);
            u64 _nd_3 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
            e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_cvar_CToggle, _nd_2));
            e.mem[_nd_3 + 1] = rfc_seal(e, _acc_1);
            r0 = 0;
            r1 = _f_1;
            r2 = _as_0;
            r3 = 0;
            r4 = term_ctr(CID_Con, _nd_3);
            _d_0 = r0;
            _cs_0 = r1;
            _as_0 = r2;
            _acc_0 = r3;
            _acc_1 = r4;
            WL_AGAIN(FID_cvar_expand_go);
          } else if (_acc_0 == 1) {
            term_sink(e, _f_1);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            term_sink(e, _f_1);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        } else if (_o_0 == 2) {
          term_sink(e, _f_1);
          term_sink(e, _as_0);
          if (_acc_0 == 0) {
            term_sink(e, _acc_1);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 1;
            r1 = _o_1;
            WL_RETN(2);
          } else if (_acc_0 == 1) {
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        } else {
          term_sink(e, _f_1);
          term_sink(e, _as_0);
          if (_acc_0 == 0) {
            term_sink(e, _acc_1);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 2;
            r1 = _o_1;
            WL_RETN(2);
          } else if (_acc_0 == 1) {
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        }
      }
    } else {
      Term _e_0 = (_d_0 - 1);
      if (term_aux(_cs_0) == CID_Nil) {
        term_sink(e, _as_0);
        r0 = _acc_0;
        r1 = _acc_1;
        WL_RETN(2);
      } else {
        Term _fb_5[2];
        u64 _sp_5 = ctr_take(e, _cs_0, 2, _fb_5);
        Term _f_8 = _fb_5[0];
        Term _f_9 = _fb_5[1];
        u32 _o_4 = 0;
        Term _o_5 = 0;
        u32 _o_6 = 0;
        Term _o_7 = 0;
        if (term_aux(_f_8) == CID_cvar_CSet) {
          _o_4 = 0;
          Term _fb_6[3];
          u64 _sp_6 = ctr_take(e, _f_8, 3, _fb_6);
          Term _f_10 = _fb_6[0];
          u32 _f_11 = _fb_6[1];
          Term _f_12 = _fb_6[2];
          spare_free(e, cls_fit(3), _sp_6);
          _o_5 = _f_10;
          _o_6 = _f_11;
          _o_7 = _f_12;
        } else if (term_aux(_f_8) == CID_cvar_CToggle) {
          _o_4 = 1;
          Term _fb_7[1];
          u64 _sp_7 = ctr_take(e, _f_8, 1, _fb_7);
          Term _f_13 = _fb_7[0];
          spare_free(e, cls_fit(1), _sp_7);
          _o_5 = _f_13;
        } else if (term_aux(_f_8) == CID_cvar_CRun) {
          _o_4 = 2;
          Term _fb_8[1];
          u64 _sp_8 = ctr_take(e, _f_8, 1, _fb_8);
          Term _f_14 = _fb_8[0];
          spare_free(e, cls_fit(1), _sp_8);
          _o_5 = _f_14;
        } else {
          _o_4 = 3;
          Term _fb_9[1];
          u64 _sp_9 = ctr_take(e, _f_8, 1, _fb_9);
          Term _f_15 = _fb_9[0];
          spare_free(e, cls_fit(1), _sp_9);
          _o_5 = _f_15;
        }
        if (_o_4 == 0) {
          if (_acc_0 == 0) {
            u64 _nd_4 = heap_alloc(e, cls_fit(3));
            e.mem[_nd_4 + 0] = rfc_seal(e, _o_5);
            e.mem[_nd_4 + 1] = rfc_seal(e, _o_6);
            e.mem[_nd_4 + 2] = rfc_seal(e, _o_7);
            u64 _nd_5 = _sp_5 >= HEAP_OFF ? _sp_5 : heap_alloc(e, cls_fit(2));
            e.mem[_nd_5 + 0] = rfc_seal(e, term_ctr(CID_cvar_CSet, _nd_4));
            e.mem[_nd_5 + 1] = rfc_seal(e, _acc_1);
            r0 = nat_chk(e, _e_0 + 1);
            r1 = _f_9;
            r2 = _as_0;
            r3 = 0;
            r4 = term_ctr(CID_Con, _nd_5);
            _d_0 = r0;
            _cs_0 = r1;
            _as_0 = r2;
            _acc_0 = r3;
            _acc_1 = r4;
            WL_AGAIN(FID_cvar_expand_go);
          } else if (_acc_0 == 1) {
            term_sink(e, _f_9);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            term_sink(e, _f_9);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        } else if (_o_4 == 1) {
          if (_acc_0 == 0) {
            u64 _nd_6 = heap_alloc(e, cls_fit(1));
            e.mem[_nd_6 + 0] = rfc_seal(e, _o_5);
            u64 _nd_7 = _sp_5 >= HEAP_OFF ? _sp_5 : heap_alloc(e, cls_fit(2));
            e.mem[_nd_7 + 0] = rfc_seal(e, term_ctr(CID_cvar_CToggle, _nd_6));
            e.mem[_nd_7 + 1] = rfc_seal(e, _acc_1);
            r0 = nat_chk(e, _e_0 + 1);
            r1 = _f_9;
            r2 = _as_0;
            r3 = 0;
            r4 = term_ctr(CID_Con, _nd_7);
            _d_0 = r0;
            _cs_0 = r1;
            _as_0 = r2;
            _acc_0 = r3;
            _acc_1 = r4;
            WL_AGAIN(FID_cvar_expand_go);
          } else if (_acc_0 == 1) {
            term_sink(e, _f_9);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            term_sink(e, _f_9);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        } else if (_o_4 == 2) {
          if (_acc_0 == 0) {
            Term _v_0 = 0;
            _as_0 = term_keep(e, _as_0, 1);
            Term _o_10[1];
            if (spin_71(e, _o_10, _as_0, _o_5) == 0) {
              return 0;
            }
            _v_0 = _o_10[0];
            _as_0 = term_keep(e, _as_0, 1);
            spare_free(e, cls_fit(2), _sp_5);
            if (seq) {
              WL_ROOM(4, 0);
              STK(0) = _e_0;
              STK(1) = _f_9;
              STK(2) = _as_0;
              STK(3) = FID_cvar_expand_go_k227;
              WL_PUSHN(4);
            } else {
              u64 _t_0 = task_node(e, FID_cvar_expand_go_k227, WL_CONT, WL_IDX, 1);
              e.mem[_t_0 + 0] = _e_0;
              e.mem[_t_0 + 1] = _f_9;
              e.mem[_t_0 + 2] = _as_0;
              WL_CONT = term_tsk(FID_cvar_expand_go_k227, _t_0);
              WL_IDX = 3;
            }
            r0 = _e_0;
            r1 = _v_0;
            r2 = _as_0;
            r3 = 0;
            r4 = _acc_1;
            _d_0 = r0;
            _cs_0 = r1;
            _as_0 = r2;
            _acc_0 = r3;
            _acc_1 = r4;
            WL_AGAIN(FID_cvar_expand_go);
          } else if (_acc_0 == 1) {
            term_sink(e, _f_9);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            term_sink(e, _f_9);
            term_sink(e, _as_0);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        } else {
          term_sink(e, _f_9);
          term_sink(e, _as_0);
          if (_acc_0 == 0) {
            term_sink(e, _acc_1);
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 2;
            r1 = _o_5;
            WL_RETN(2);
          } else if (_acc_0 == 1) {
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 1;
            r1 = _acc_1;
            WL_RETN(2);
          } else {
            spare_free(e, cls_fit(2), _sp_5);
            r0 = 2;
            r1 = _acc_1;
            WL_RETN(2);
          }
        }
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cvar_expand_go_k227)
    WL_POPN(3);
    Term _e_1 = STK(0);
    Term _f_16 = STK(1);
    Term _as_2 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_cvar_expand_go)) {
      u64 _t_1 = task_node(e, FID_cvar_expand_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = nat_chk(e, _e_1 + 1);
      e.mem[_t_1 + 1] = _f_16;
      e.mem[_t_1 + 2] = _as_2;
      e.mem[_t_1 + 3] = _h_0;
      e.mem[_t_1 + 4] = _h_1;
      return term_tsk(FID_cvar_expand_go, _t_1);
    }
    r0 = nat_chk(e, _e_1 + 1);
    r1 = _f_16;
    r2 = _as_2;
    r3 = _h_0;
    r4 = _h_1;
    WL_JMP(FID_cvar_expand_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_alias)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_alias_k236;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_alias_k236, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_alias_k236, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_alias_k236)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_cvar_get_alias_k237;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_cvar_get_alias_k237, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_cvar_get_alias_k237, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_cmds)) {
        u64 _t_3 = task_node(e, FID_ffi_cvar_get_cmds, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_cvar_get_cmds, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_cvar_get_cmds);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_alias_k237)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_62(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_3)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    Term _cur_3 = r4;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_cvar_Alias, _nd_0));
        e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_1);
        r2 = _cur_3;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = _cur_2;
          STK(3) = FID_wire_get_list_go_3_k239;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_3_k239, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          WL_CONT = term_tsk(FID_wire_get_list_go_3_k239, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_alias)) {
          u64 _t_1 = task_node(e, FID_ffi_cvar_get_alias, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_3;
          return term_tsk(FID_ffi_cvar_get_alias, _t_1);
        }
        r0 = _cur_3;
        WL_JMP(FID_ffi_cvar_get_alias);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_3_k239)
    WL_POPN(3);
    Term _m_1 = STK(0);
    Term _cur_4 = STK(1);
    Term _cur_5 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _cur_4;
      STK(1) = _cur_5;
      STK(2) = FID_wire_get_list_go_3_k240;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_3_k240, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_4;
      e.mem[_t_2 + 1] = _cur_5;
      WL_CONT = term_tsk(FID_wire_get_list_go_3_k240, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_3)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_3, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      return term_tsk(FID_wire_get_list_go_3, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    WL_JMP(FID_wire_get_list_go_3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_3_k240)
    WL_POPN(2);
    Term _cur_6 = STK(0);
    Term _cur_7 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_73(e, _o_0, _cur_6, _cur_7, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_cdig_go)
    Term _ds_0 = r0;
    u32 _x_0 = r1;
    Term _i_0 = r2;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ds_0) == CID_Nil) {
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ds_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_0;
        STK(1) = _x_0;
        STK(2) = _i_0;
        STK(3) = FID_wire_cdig_go_k246;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_cdig_go_k246, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _x_0;
        e.mem[_t_0 + 2] = _i_0;
        WL_CONT = term_tsk(FID_wire_cdig_go_k246, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      r1 = _x_0;
      r2 = nat_chk(e, _i_0 + 1);
      _ds_0 = r0;
      _x_0 = r1;
      _i_0 = r2;
      WL_AGAIN(FID_wire_cdig_go);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_cdig_go_k246)
    WL_POPN(3);
    u32 _f_2 = STK(0);
    u32 _x_1 = STK(1);
    Term _i_1 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_74(e, _o_0, U32_BIN(_x_1, ==, _f_2), _h_0, _h_1, _i_1) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_go)
    Term _k_0 = r0;
    u32 _ts_0 = r1;
    Term _ts_1 = r2;
    Term _ts_2 = r3;
    Term _ds_0 = r4;
    WL_OPEN
    if (_k_0 == 0) {
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat_end)) {
        u64 _t_0 = task_node(e, FID_wire_get_nat_end, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _ts_0;
        e.mem[_t_0 + 1] = _ts_1;
        e.mem[_t_0 + 2] = _ts_2;
        e.mem[_t_0 + 3] = _ds_0;
        return term_tsk(FID_wire_get_nat_end, _t_0);
      }
      r0 = _ts_0;
      r1 = _ts_1;
      r2 = _ts_2;
      r3 = _ds_0;
      WL_JMP(FID_wire_get_nat_end);
    } else {
      Term _j_0 = (_k_0 - 1);
      if (_ts_0 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _j_0;
          STK(1) = _ts_1;
          STK(2) = _ds_0;
          STK(3) = FID_wire_get_nat_go_k249;
          WL_PUSHN(4);
        } else {
          u64 _t_1 = task_node(e, FID_wire_get_nat_go_k249, WL_CONT, WL_IDX, 1);
          e.mem[_t_1 + 0] = _j_0;
          e.mem[_t_1 + 1] = _ts_1;
          e.mem[_t_1 + 2] = _ds_0;
          WL_CONT = term_tsk(FID_wire_get_nat_go_k249, _t_1);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_peek)) {
          u64 _t_2 = task_node(e, FID_wire_peek, WL_CONT, WL_IDX, 0);
          e.mem[_t_2 + 0] = _ts_2;
          return term_tsk(FID_wire_peek, _t_2);
        }
        r0 = _ts_2;
        WL_JMP(FID_wire_peek);
      } else if (_ts_0 == 1) {
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _ts_2;
          STK(1) = FID_wire_get_nat_go_k250;
          WL_PUSHN(2);
        } else {
          u64 _t_4 = task_node(e, FID_wire_get_nat_go_k250, WL_CONT, WL_IDX, 1);
          e.mem[_t_4 + 0] = _ts_2;
          WL_CONT = term_tsk(FID_wire_get_nat_go_k250, _t_4);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_value)) {
          u64 _t_5 = task_node(e, FID_wire_value, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _ds_0;
          return term_tsk(FID_wire_value, _t_5);
        }
        r0 = _ds_0;
        WL_JMP(FID_wire_value);
      } else {
        term_sink(e, _ts_2);
        term_sink(e, _ds_0);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_go_k249)
    WL_POPN(3);
    Term _j_1 = STK(0);
    Term _ts_3 = STK(1);
    Term _ds_1 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _ts_3);
    e.mem[_nd_0 + 1] = rfc_seal(e, _ds_1);
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat_go)) {
      u64 _t_3 = task_node(e, FID_wire_get_nat_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _j_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = term_ctr(CID_Con, _nd_0);
      return term_tsk(FID_wire_get_nat_go, _t_3);
    }
    r0 = _j_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = term_ctr(CID_Con, _nd_0);
    WL_JMP(FID_wire_get_nat_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_go_k250)
    WL_POPN(1);
    Term _ts_4 = STK(0);
    Term _h_3 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _h_3;
    r2 = _ts_4;
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_end)
    u32 _ts_0 = r0;
    Term _ts_1 = r1;
    Term _ts_2 = r2;
    Term _ds_0 = r3;
    WL_OPEN
    if (_ts_0 == 0) {
      term_sink(e, _ts_2);
      term_sink(e, _ds_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    } else if (_ts_0 == 1) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _ts_2;
        STK(1) = FID_wire_get_nat_end_k252;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_get_nat_end_k252, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _ts_2;
        WL_CONT = term_tsk(FID_wire_get_nat_end_k252, _t_0);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_value)) {
        u64 _t_1 = task_node(e, FID_wire_value, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _ds_0;
        return term_tsk(FID_wire_value, _t_1);
      }
      r0 = _ds_0;
      WL_JMP(FID_wire_value);
    } else {
      term_sink(e, _ts_2);
      term_sink(e, _ds_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_end_k252)
    WL_POPN(1);
    Term _ts_3 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _h_0;
    r2 = _ts_3;
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_str)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_str_k261;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_str_k261, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_str_k261, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_str_k261)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (!DEVICE && !seq && fid_nofk(FID_wire_take)) {
        u64 _t_2 = task_node(e, FID_wire_take, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = _h_1;
        e.mem[_t_2 + 1] = _h_2;
        return term_tsk(FID_wire_take, _t_2);
      }
      r0 = _h_1;
      r1 = _h_2;
      WL_JMP(FID_wire_take);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_1)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_0);
        r2 = _cur_2;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = FID_wire_get_list_go_1_k263;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_1_k263, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          WL_CONT = term_tsk(FID_wire_get_list_go_1_k263, _t_0);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
          u64 _t_1 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_2;
          return term_tsk(FID_wire_get_str, _t_1);
        }
        r0 = _cur_2;
        WL_JMP(FID_wire_get_str);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_1_k263)
    WL_POPN(2);
    Term _m_1 = STK(0);
    Term _cur_3 = STK(1);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _cur_3;
      STK(1) = FID_wire_get_list_go_1_k264;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_1_k264, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_3;
      WL_CONT = term_tsk(FID_wire_get_list_go_1_k264, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_1)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      return term_tsk(FID_wire_get_list_go_1, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    WL_JMP(FID_wire_get_list_go_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_1_k264)
    WL_POPN(1);
    Term _cur_4 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_76(e, _o_0, _cur_4, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_0)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_0_k266;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_0_k266, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_0_k266, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_0_k266)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_0_k267;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_0_k267, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_0_k267, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_env_get_var)) {
          u64 _t_3 = task_node(e, FID_ffi_child_env_get_var, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_child_env_get_var, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_child_env_get_var);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_0_k267)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_0)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      return term_tsk(FID_wire_get_list_go_0, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    WL_JMP(FID_wire_get_list_go_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_child)
    Term _reg_0 = r0;
    Term _ks_0 = r1;
    Term _base_0 = r2;
    Term _over_0 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _reg_0;
      STK(1) = _ks_0;
      STK(2) = FID_child_env_child_k271;
      WL_PUSHN(3);
    } else {
      u64 _t_0 = task_node(e, FID_child_env_child_k271, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _reg_0;
      e.mem[_t_0 + 1] = _ks_0;
      WL_CONT = term_tsk(FID_child_env_child_k271, _t_0);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_child_env_merge)) {
      u64 _t_1 = task_node(e, FID_child_env_merge, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _base_0;
      e.mem[_t_1 + 1] = _over_0;
      return term_tsk(FID_child_env_merge, _t_1);
    }
    r0 = _base_0;
    r1 = _over_0;
    WL_JMP(FID_child_env_merge);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_child_env_child_k271)
    WL_POPN(2);
    Term _reg_1 = STK(0);
    Term _ks_1 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_child_env_keep)) {
      u64 _t_2 = task_node(e, FID_child_env_keep, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _reg_1;
      e.mem[_t_2 + 1] = _ks_1;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_child_env_keep, _t_2);
    }
    r0 = _reg_1;
    r1 = _ks_1;
    r2 = _h_0;
    WL_JMP(FID_child_env_keep);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_6)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_6_k278;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_6_k278, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_6_k278, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_6_k278)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_6_k279;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_6_k279, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_6_k279, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_verdict)) {
          u64 _t_3 = task_node(e, FID_ffi_director_get_verdict, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_director_get_verdict, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_director_get_verdict);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_6_k279)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_6)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_6, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      e.mem[_t_4 + 5] = _h_7;
      return term_tsk(FID_wire_get_list_go_6, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    WL_JMP(FID_wire_get_list_go_6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_tick)
    Term _cap_0 = r0;
    Term _l_0 = r1;
    Term _l_1 = r2;
    u32 _l_2 = r3;
    u32 _l_3 = r4;
    Term _vs_0 = r5;
    WL_OPEN
    if (_l_2 == 0) {
      _l_1 = term_keep(e, _l_1, 1);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _cap_0;
        STK(1) = _l_0;
        STK(2) = _l_1;
        STK(3) = _vs_0;
        STK(4) = FID_director_tick_k282;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_director_tick_k282, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _cap_0;
        e.mem[_t_0 + 1] = _l_0;
        e.mem[_t_0 + 2] = _l_1;
        e.mem[_t_0 + 3] = _vs_0;
        WL_CONT = term_tsk(FID_director_tick_k282, _t_0);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_director_decide)) {
        u64 _t_1 = task_node(e, FID_director_decide, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _l_1;
        e.mem[_t_1 + 1] = _vs_0;
        e.mem[_t_1 + 2] = _cap_0;
        return term_tsk(FID_director_decide, _t_1);
      }
      r0 = _l_1;
      r1 = _vs_0;
      r2 = _cap_0;
      WL_JMP(FID_director_decide);
    } else {
      term_sink(e, _vs_0);
      r0 = _l_0;
      r1 = _l_1;
      r2 = 1;
      r3 = _l_3;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_tick_k282)
    WL_POPN(4);
    Term _cap_1 = STK(0);
    Term _l_4 = STK(1);
    Term _l_5 = STK(2);
    Term _vs_1 = STK(3);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    if (_h_0 == 0) {
      if (_l_4 == 0) {
        term_sink(e, _h_1);
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_director_tick_k283;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_director_tick_k283, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_director_tick_k283, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_director_kept)) {
          u64 _t_3 = task_node(e, FID_director_kept, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _l_5;
          e.mem[_t_3 + 1] = _vs_1;
          e.mem[_t_3 + 2] = _cap_1;
          return term_tsk(FID_director_kept, _t_3);
        }
        r0 = _l_5;
        r1 = _vs_1;
        r2 = _cap_1;
        WL_JMP(FID_director_kept);
      } else {
        Term _m_0 = (_l_4 - 1);
        term_sink(e, _l_5);
        term_sink(e, _vs_1);
        r0 = _m_0;
        r1 = _h_1;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      }
    } else if (_h_0 == 1) {
      term_sink(e, _h_1);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _l_4;
        STK(1) = FID_director_tick_k284;
        WL_PUSHN(2);
      } else {
        u64 _t_4 = task_node(e, FID_director_tick_k284, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _l_4;
        WL_CONT = term_tsk(FID_director_tick_k284, _t_4);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_director_kept)) {
        u64 _t_5 = task_node(e, FID_director_kept, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _l_5;
        e.mem[_t_5 + 1] = _vs_1;
        e.mem[_t_5 + 2] = _cap_1;
        return term_tsk(FID_director_kept, _t_5);
      }
      r0 = _l_5;
      r1 = _vs_1;
      r2 = _cap_1;
      WL_JMP(FID_director_kept);
    } else {
      term_sink(e, _h_1);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _l_4;
        STK(1) = FID_director_tick_k285;
        WL_PUSHN(2);
      } else {
        u64 _t_6 = task_node(e, FID_director_tick_k285, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _l_4;
        WL_CONT = term_tsk(FID_director_tick_k285, _t_6);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_director_kept)) {
        u64 _t_7 = task_node(e, FID_director_kept, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _l_5;
        e.mem[_t_7 + 1] = _vs_1;
        e.mem[_t_7 + 2] = _cap_1;
        return term_tsk(FID_director_kept, _t_7);
      }
      r0 = _l_5;
      r1 = _vs_1;
      r2 = _cap_1;
      WL_JMP(FID_director_kept);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_tick_k283)
    Term _h_2 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _h_2;
    r2 = 1;
    r3 = 1;
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_tick_k284)
    WL_POPN(1);
    Term _l_6 = STK(0);
    Term _h_3 = r0;
    WL_OPEN
    r0 = _l_6;
    r1 = _h_3;
    r2 = 1;
    r3 = 1;
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_director_tick_k285)
    WL_POPN(1);
    Term _l_7 = STK(0);
    Term _h_4 = r0;
    WL_OPEN
    r0 = _l_7;
    r1 = _h_4;
    r2 = 1;
    r3 = 2;
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_bind)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_bind_k289;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_bind_k289, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_bind_k289, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_bind_k289)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_cvar_get_bind_k290;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_cvar_get_bind_k290, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_cvar_get_bind_k290, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_cmds)) {
        u64 _t_3 = task_node(e, FID_ffi_cvar_get_cmds, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_cvar_get_cmds, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_cvar_get_cmds);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_bind_k290)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_69(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_4)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    Term _cur_3 = r4;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_cvar_KeyBind, _nd_0));
        e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        r0 = 0;
        r1 = term_ctr(CID_Con, _nd_1);
        r2 = _cur_3;
        WL_RETN(3);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    } else {
      Term _m_0 = (_n_0 - 1);
      if (_cur_0 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _m_0;
          STK(1) = _cur_1;
          STK(2) = _cur_2;
          STK(3) = FID_wire_get_list_go_4_k292;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_4_k292, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          WL_CONT = term_tsk(FID_wire_get_list_go_4_k292, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_bind)) {
          u64 _t_1 = task_node(e, FID_ffi_cvar_get_bind, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_3;
          return term_tsk(FID_ffi_cvar_get_bind, _t_1);
        }
        r0 = _cur_3;
        WL_JMP(FID_ffi_cvar_get_bind);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        WL_RETN(3);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_4_k292)
    WL_POPN(3);
    Term _m_1 = STK(0);
    Term _cur_4 = STK(1);
    Term _cur_5 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _cur_4;
      STK(1) = _cur_5;
      STK(2) = FID_wire_get_list_go_4_k293;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_4_k293, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_4;
      e.mem[_t_2 + 1] = _cur_5;
      WL_CONT = term_tsk(FID_wire_get_list_go_4_k293, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_4)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_4, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      return term_tsk(FID_wire_get_list_go_4, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    WL_JMP(FID_wire_get_list_go_4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_4_k293)
    WL_POPN(2);
    Term _cur_6 = STK(0);
    Term _cur_7 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_79(e, _o_0, _cur_6, _cur_7, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_U32_show_go)
    Term _f_0 = r0;
    u32 _n_0 = r1;
    Term _acc_0 = r2;
    WL_OPEN
    WL_SPIN
    if (_f_0 == 0) {
      r0 = _acc_0;
      WL_RETN(1);
    } else {
      Term _g_0 = (_f_0 - 1);
      u32 _s_0 = U32_BIN(_n_0, ==, 0);
      if (_s_0 == 1) {
        r0 = _acc_0;
        WL_RETN(1);
      } else {
        Term _a_0 = 10ull;
        Term _a_1 = 10ull;
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, U32_BIN(48ull, +, ((u32)(_a_1) == 0 ? _n_0 : U32_BIN(_n_0, -, U32_QUO((u32)(_n_0), (u32)(_a_1)) * _a_1))));
        e.mem[_nd_0 + 1] = rfc_seal(e, _acc_0);
        r0 = _g_0;
        r1 = ((u32)(_a_0) == 0 ? 0 : (u64)U32_QUO((u32)(_n_0), (u32)(_a_0)));
        r2 = term_ctr(CID_SCon, _nd_0);
        _f_0 = r0;
        _n_0 = r1;
        _acc_0 = r2;
        WL_AGAIN(FID_U32_show_go);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cvar_expand)
    Term _cs_0 = r0;
    Term _as_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _cs_0;
      STK(1) = _as_0;
      STK(2) = FID_cvar_expand_k297;
      WL_PUSHN(3);
    } else {
      u64 _t_0 = task_node(e, FID_cvar_expand_k297, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _cs_0;
      e.mem[_t_0 + 1] = _as_0;
      WL_CONT = term_tsk(FID_cvar_expand_k297, _t_0);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
      u64 _t_1 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _as_0;
      return term_tsk(FID_List_length, _t_1);
    }
    r0 = _as_0;
    WL_JMP(FID_List_length);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cvar_expand_k297)
    WL_POPN(2);
    Term _cs_1 = STK(0);
    Term _as_1 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_cvar_expand_k298;
      WL_PUSHN(1);
    } else {
      u64 _t_2 = task_node(e, FID_cvar_expand_k298, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_cvar_expand_k298, _t_2);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_cvar_expand_go)) {
      u64 _t_3 = task_node(e, FID_cvar_expand_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = nat_chk(e, _h_0 + 1);
      e.mem[_t_3 + 1] = _cs_1;
      e.mem[_t_3 + 2] = _as_1;
      e.mem[_t_3 + 3] = 0;
      e.mem[_t_3 + 4] = term_pak(CID_Nil, 0);
      return term_tsk(FID_cvar_expand_go, _t_3);
    }
    r0 = nat_chk(e, _h_0 + 1);
    r1 = _cs_1;
    r2 = _as_1;
    r3 = 0;
    r4 = term_pak(CID_Nil, 0);
    WL_JMP(FID_cvar_expand_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cvar_expand_k298)
    u32 _h_1 = r0;
    Term _h_2 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_81(e, _o_1, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_put_cmds)
    Term _cs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_put_cmds_k300;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_put_cmds_k300, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_put_cmds_k300, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_2)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_2, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _cs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_2, _t_1);
    }
    r0 = _cs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_put_cmds_k300)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[1];
    if (spin_52(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmds)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_cmds_k306;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_cmds_k306, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_cmds_k306, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmds_k306)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_ffi_cvar_get_cmds_k307;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_cvar_get_cmds_k307, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_ffi_cvar_get_cmds_k307, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_cmd)) {
          u64 _t_3 = task_node(e, FID_ffi_cvar_get_cmd, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_cvar_get_cmd, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_cvar_get_cmd);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_cmds_k307)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    u32 _h_6 = r3;
    Term _h_7 = r4;
    Term _h_8 = r5;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_2)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_2, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      e.mem[_t_4 + 5] = _h_7;
      e.mem[_t_4 + 6] = _h_8;
      return term_tsk(FID_wire_get_list_go_2, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    r6 = _h_8;
    WL_JMP(FID_wire_get_list_go_2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_tok)
    u32 _c_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _c_0;
      STK(1) = FID_wire_tok_k312;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_wire_tok_k312, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _c_0;
      WL_CONT = term_tsk(FID_wire_tok_k312, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_cdig_go)) {
      u64 _t_1 = task_node(e, FID_wire_cdig_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = term_ctr(CID_Con, STAT_OFF + 216);
      e.mem[_t_1 + 1] = _c_0;
      e.mem[_t_1 + 2] = 0;
      return term_tsk(FID_wire_cdig_go, _t_1);
    }
    r0 = term_ctr(CID_Con, STAT_OFF + 216);
    r1 = _c_0;
    r2 = 0;
    WL_JMP(FID_wire_cdig_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_tok_k312)
    WL_POPN(1);
    u32 _c_1 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_83(e, _o_1, _h_0, _h_1, U32_BIN(_c_1, ==, 44ull)) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_loop)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_director_get_loop_k330;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_director_get_loop_k330, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_director_get_loop_k330, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_loop_k330)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_director_get_loop_k331;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_director_get_loop_k331, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_director_get_loop_k331, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_5)) {
        u64 _t_3 = task_node(e, FID_wire_get_list_5, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_list_5, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_list_5);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_loop_k331)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_6;
        STK(1) = _h_4;
        STK(2) = FID_ffi_director_get_loop_k332;
        WL_PUSHN(3);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_director_get_loop_k332, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_6;
        e.mem[_t_4 + 1] = _h_4;
        WL_CONT = term_tsk(FID_ffi_director_get_loop_k332, _t_4);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_end)) {
        u64 _t_5 = task_node(e, FID_ffi_director_get_end, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_ffi_director_get_end, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_ffi_director_get_end);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_loop_k332)
    WL_POPN(2);
    Term _h_11 = STK(0);
    Term _h_12 = STK(1);
    u32 _h_7 = r0;
    u32 _h_8 = r1;
    u32 _h_9 = r2;
    Term _h_10 = r3;
    WL_OPEN
    Term _o_0[6];
    if (spin_67(e, _o_0, _h_11, _h_12, _h_7, _h_8, _h_9, _h_10) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = (u32)_o_0[3];
    r4 = (u32)_o_0[4];
    r5 = _o_0[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cvar_press)
    Term _bs_0 = r0;
    Term _k_0 = r1;
    Term _as_0 = r2;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_2[1];
    if (spin_86(e, _o_2, _bs_0, _k_0) == 0) {
      return 0;
    }
    _v_0 = _o_2[0];
    if (!DEVICE && !seq && fid_nofk(FID_cvar_expand)) {
      u64 _t_0 = task_node(e, FID_cvar_expand, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _v_0;
      e.mem[_t_0 + 1] = _as_0;
      return term_tsk(FID_cvar_expand, _t_0);
    }
    r0 = _v_0;
    r1 = _as_0;
    WL_JMP(FID_cvar_expand);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_put_exp)
    u32 _e_0 = r0;
    Term _e_1 = r1;
    Term _rest_0 = r2;
    WL_OPEN
    if (_e_0 == 0) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_cvar_put_exp_k345;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_cvar_put_exp_k345, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_cvar_put_exp_k345, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_put_cmds)) {
        u64 _t_1 = task_node(e, FID_ffi_cvar_put_cmds, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _e_1;
        e.mem[_t_1 + 1] = _rest_0;
        return term_tsk(FID_ffi_cvar_put_cmds, _t_1);
      }
      r0 = _e_1;
      r1 = _rest_0;
      WL_JMP(FID_ffi_cvar_put_cmds);
    } else if (_e_0 == 1) {
      Term _v_0 = 0;
      Term _o_1[1];
      if (spin_10(e, _o_1, _e_1, _rest_0) == 0) {
        return 0;
      }
      _v_0 = _o_1[0];
      Term _o_2[1];
      if (spin_10(e, _o_2, 1ull, _v_0) == 0) {
        return 0;
      }
      r0 = _o_2[0];
      WL_RETN(1);
    } else {
      Term _v_1 = 0;
      Term _o_3[1];
      if (spin_10(e, _o_3, _e_1, _rest_0) == 0) {
        return 0;
      }
      _v_1 = _o_3[0];
      Term _o_4[1];
      if (spin_10(e, _o_4, 2ull, _v_1) == 0) {
        return 0;
      }
      r0 = _o_4[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_put_exp_k345)
    Term _h_0 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_10(e, _o_0, 0, _h_0) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_Nat_show_fin)
    Term _g_0 = r0;
    Term _acc_0 = r1;
    u32 _dq_0 = r2;
    Term _dq_1 = r3;
    WL_OPEN
    WL_SPIN
    if (_dq_1 == 0) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _dq_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _acc_0);
      r0 = term_ctr(CID_SCon, _nd_0);
      WL_RETN(1);
    } else {
      Term _p_0 = (_dq_1 - 1);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, _dq_0);
      e.mem[_nd_1 + 1] = rfc_seal(e, _acc_0);
      if (_g_0 == 0) {
        Term _n_0 = nat_chk(e, _p_0 + 1);
        Term _acc_1 = term_ctr(CID_SCon, _nd_1);
        r0 = _acc_1;
        WL_RETN(1);
      } else {
        Term _g_1 = (_g_0 - 1);
        Term _n_1 = nat_chk(e, _p_0 + 1);
        Term _acc_2 = term_ctr(CID_SCon, _nd_1);
        u32 _v_0 = 0;
        Term _v_1 = 0;
        Term _a_0 = 10ull;
        Term _a_1 = (_a_0 == 0 ? 0 : _n_1 / _a_0);
        Term _a_2 = (_a_0 == 0 ? _n_1 : _n_1 % _a_0);
        Term _o_0[2];
        if (spin_82(e, _o_0, _a_1, _a_2) == 0) {
          return 0;
        }
        _v_0 = (u32)_o_0[0];
        _v_1 = _o_0[1];
        r0 = _g_1;
        r1 = _acc_2;
        r2 = _v_0;
        r3 = _v_1;
        _g_0 = r0;
        _acc_0 = r1;
        _dq_0 = r2;
        _dq_1 = r3;
        WL_AGAIN(FID_Nat_show_fin);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_3)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_3_k349;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_3_k349, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_3_k349, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_3_k349)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_3_k350;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_3_k350, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_3_k350, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_alias)) {
          u64 _t_3 = task_node(e, FID_ffi_cvar_get_alias, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_cvar_get_alias, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_cvar_get_alias);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_3_k350)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_3)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_3, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      return term_tsk(FID_wire_get_list_go_3, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    WL_JMP(FID_wire_get_list_go_3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_peek)
    Term _s_0 = r0;
    WL_OPEN
    if (term_aux(_s_0) == CID_SNil) {
      r0 = 2;
      r1 = 0;
      r2 = term_pak(CID_SNil, 0);
      WL_RETN(3);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_0, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_1;
        STK(1) = FID_wire_peek_k356;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_peek_k356, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        WL_CONT = term_tsk(FID_wire_peek_k356, _t_0);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_tok)) {
        u64 _t_1 = task_node(e, FID_wire_tok, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _f_0;
        return term_tsk(FID_wire_tok, _t_1);
      }
      r0 = _f_0;
      WL_JMP(FID_wire_tok);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_peek_k356)
    WL_POPN(1);
    Term _f_2 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    r0 = _h_0;
    r1 = _h_1;
    r2 = _f_2;
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_u32)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_u32_k361;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_u32_k361, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_u32_k361, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_u32_k361)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_2[3];
    if (spin_88(e, _o_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_1)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_1_k368;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_1_k368, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_1_k368, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_1_k368)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_1_k369;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_1_k369, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_1_k369, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
          u64 _t_3 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_wire_get_str, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_str);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_1_k369)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_1)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      return term_tsk(FID_wire_get_list_go_1, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    WL_JMP(FID_wire_get_list_go_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_4)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_4_k384;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_4_k384, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_4_k384, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_4_k384)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        r0 = 0;
        r1 = term_pak(CID_Nil, 0);
        r2 = _h_2;
        WL_RETN(3);
      } else {
        Term _m_0 = (_h_1 - 1);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _m_0;
          STK(1) = FID_wire_get_list_4_k385;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_4_k385, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_4_k385, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_bind)) {
          u64 _t_3 = task_node(e, FID_ffi_cvar_get_bind, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_cvar_get_bind, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_cvar_get_bind);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_4_k385)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_4)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_4, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      return term_tsk(FID_wire_get_list_go_4, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    WL_JMP(FID_wire_get_list_go_4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_U32_show)
    u32 _a_0 = r0;
    WL_OPEN
    u32 _s_0 = U32_BIN(_a_0, ==, 0);
    if (_s_0 == 1) {
      r0 = term_ctr(CID_SCon, STAT_OFF + 220);
      WL_RETN(1);
    } else {
      if (!DEVICE && !seq && fid_nofk(FID_U32_show_go)) {
        u64 _t_0 = task_node(e, FID_U32_show_go, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = 10ull;
        e.mem[_t_0 + 1] = _a_0;
        e.mem[_t_0 + 2] = term_pak(CID_SNil, 0);
        return term_tsk(FID_U32_show_go, _t_0);
      }
      r0 = 10ull;
      r1 = _a_0;
      r2 = term_pak(CID_SNil, 0);
      WL_JMP(FID_U32_show_go);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_Nat_show)
    Term _n_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _v_1 = 0;
    Term _a_0 = 10ull;
    Term _a_1 = (_a_0 == 0 ? 0 : _n_0 / _a_0);
    Term _a_2 = (_a_0 == 0 ? _n_0 : _n_0 % _a_0);
    Term _o_0[2];
    if (spin_82(e, _o_0, _a_1, _a_2) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    _v_1 = _o_0[1];
    if (!DEVICE && !seq && fid_nofk(FID_Nat_show_fin)) {
      u64 _t_0 = task_node(e, FID_Nat_show_fin, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _n_0;
      e.mem[_t_0 + 1] = term_pak(CID_SNil, 0);
      e.mem[_t_0 + 2] = _v_0;
      e.mem[_t_0 + 3] = _v_1;
      return term_tsk(FID_Nat_show_fin, _t_0);
    }
    r0 = _n_0;
    r1 = term_pak(CID_SNil, 0);
    r2 = _v_0;
    r3 = _v_1;
    WL_JMP(FID_Nat_show_fin);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_String_append)
    Term _a_0 = r0;
    Term _b_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_a_0) == CID_SNil) {
      r0 = _b_0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _a_0, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_String_append_k396;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_String_append_k396, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_String_append_k396, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      r1 = _b_0;
      _a_0 = r0;
      _b_0 = r1;
      WL_AGAIN(FID_String_append);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_String_append_k396)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _f_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_SCon, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_xreq)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_xreq_k398;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_xreq_k398, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_xreq_k398, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_3)) {
      u64 _t_1 = task_node(e, FID_wire_get_list_3, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_3, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_xreq_k398)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_cvar_get_xreq_k399;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_cvar_get_xreq_k399, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_cvar_get_xreq_k399, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_cmds)) {
        u64 _t_3 = task_node(e, FID_ffi_cvar_get_cmds, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_cvar_get_cmds, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_cvar_get_cmds);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_xreq_k399)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_87(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_nat_k403;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_nat_k403, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_nat_k403, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_peek)) {
      u64 _t_1 = task_node(e, FID_wire_peek, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_peek, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_peek);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_k403)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_wire_get_nat_k404;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_wire_get_nat_k404, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_wire_get_nat_k404, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_peek)) {
        u64 _t_3 = task_node(e, FID_wire_peek, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_peek, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_peek);
    } else if (_h_0 == 1) {
      term_sink(e, _h_2);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    } else {
      term_sink(e, _h_2);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat_k404)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_6 == 0) {
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat_end)) {
        u64 _t_4 = task_node(e, FID_wire_get_nat_end, WL_CONT, WL_IDX, 0);
        e.mem[_t_4 + 0] = _h_3;
        e.mem[_t_4 + 1] = _h_4;
        e.mem[_t_4 + 2] = _h_5;
        e.mem[_t_4 + 3] = term_ctr(CID_Con, STAT_OFF + 218);
        return term_tsk(FID_wire_get_nat_end, _t_4);
      }
      r0 = _h_3;
      r1 = _h_4;
      r2 = _h_5;
      r3 = term_ctr(CID_Con, STAT_OFF + 218);
      WL_JMP(FID_wire_get_nat_end);
    } else {
      Term _p_0 = (_h_6 - 1);
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, nat_chk(e, _p_0 + 1));
      e.mem[_nd_0 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat_go)) {
        u64 _t_5 = task_node(e, FID_wire_get_nat_go, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = 13ull;
        e.mem[_t_5 + 1] = _h_3;
        e.mem[_t_5 + 2] = _h_4;
        e.mem[_t_5 + 3] = _h_5;
        e.mem[_t_5 + 4] = term_ctr(CID_Con, _nd_0);
        return term_tsk(FID_wire_get_nat_go, _t_5);
      }
      r0 = 13ull;
      r1 = _h_3;
      r2 = _h_4;
      r3 = _h_5;
      r4 = term_ctr(CID_Con, _nd_0);
      WL_JMP(FID_wire_get_nat_go);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_env_get_req_k412;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_env_get_req_k412, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_env_get_req_k412, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_1)) {
      u64 _t_1 = task_node(e, FID_wire_get_list_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_1, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_req_k412)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_child_env_get_req_k413;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_child_env_get_req_k413, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_child_env_get_req_k413, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_1)) {
        u64 _t_3 = task_node(e, FID_wire_get_list_1, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_list_1, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_list_1);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_req_k413)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_6;
        STK(1) = _h_4;
        STK(2) = FID_ffi_child_env_get_req_k414;
        WL_PUSHN(3);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_child_env_get_req_k414, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_6;
        e.mem[_t_4 + 1] = _h_4;
        WL_CONT = term_tsk(FID_ffi_child_env_get_req_k414, _t_4);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
        u64 _t_5 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_wire_get_list_0, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_wire_get_list_0);
    } else {
      term_sink(e, _h_6);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_req_k414)
    WL_POPN(2);
    Term _h_10 = STK(0);
    Term _h_11 = STK(1);
    u32 _h_7 = r0;
    Term _h_8 = r1;
    Term _h_9 = r2;
    WL_OPEN
    if (_h_7 == 0) {
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _h_10;
        STK(1) = _h_11;
        STK(2) = _h_8;
        STK(3) = FID_ffi_child_env_get_req_k415;
        WL_PUSHN(4);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_child_env_get_req_k415, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _h_10;
        e.mem[_t_6 + 1] = _h_11;
        e.mem[_t_6 + 2] = _h_8;
        WL_CONT = term_tsk(FID_ffi_child_env_get_req_k415, _t_6);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
        u64 _t_7 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _h_9;
        return term_tsk(FID_wire_get_list_0, _t_7);
      }
      r0 = _h_9;
      WL_JMP(FID_wire_get_list_0);
    } else {
      term_sink(e, _h_10);
      term_sink(e, _h_11);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      WL_RETN(6);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_env_get_req_k415)
    WL_POPN(3);
    Term _h_15 = STK(0);
    Term _h_16 = STK(1);
    Term _h_17 = STK(2);
    u32 _h_12 = r0;
    Term _h_13 = r1;
    Term _h_14 = r2;
    WL_OPEN
    Term _o_0[6];
    if (spin_77(e, _o_0, _h_15, _h_16, _h_17, _h_12, _h_13, _h_14) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_director_get_req_k420;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_director_get_req_k420, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_director_get_req_k420, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
      u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_req_k420)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_director_get_req_k421;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_director_get_req_k421, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_director_get_req_k421, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_loop)) {
        u64 _t_3 = task_node(e, FID_ffi_director_get_loop, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_director_get_loop, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_director_get_loop);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      WL_RETN(8);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_req_k421)
    WL_POPN(1);
    Term _h_9 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    u32 _h_6 = r3;
    u32 _h_7 = r4;
    Term _h_8 = r5;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _h_9;
        STK(1) = _h_4;
        STK(2) = _h_5;
        STK(3) = _h_6;
        STK(4) = _h_7;
        STK(5) = FID_ffi_director_get_req_k422;
        WL_PUSHN(6);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_director_get_req_k422, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_9;
        e.mem[_t_4 + 1] = _h_4;
        e.mem[_t_4 + 2] = _h_5;
        e.mem[_t_4 + 3] = _h_6;
        e.mem[_t_4 + 4] = _h_7;
        WL_CONT = term_tsk(FID_ffi_director_get_req_k422, _t_4);
        WL_IDX = 5;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_6)) {
        u64 _t_5 = task_node(e, FID_wire_get_list_6, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_8;
        return term_tsk(FID_wire_get_list_6, _t_5);
      }
      r0 = _h_8;
      WL_JMP(FID_wire_get_list_6);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      WL_RETN(8);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_director_get_req_k422)
    WL_POPN(5);
    Term _h_13 = STK(0);
    Term _h_14 = STK(1);
    Term _h_15 = STK(2);
    u32 _h_16 = STK(3);
    u32 _h_17 = STK(4);
    u32 _h_10 = r0;
    Term _h_11 = r1;
    Term _h_12 = r2;
    WL_OPEN
    Term _o_0[8];
    if (spin_85(e, _o_0, _h_13, _h_14, _h_15, _h_16, _h_17, _h_10, _h_11, _h_12) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = (u32)_o_0[4];
    r5 = (u32)_o_0[5];
    r6 = _o_0[6];
    r7 = _o_0[7];
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_table)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_get_table_k427;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_get_table_k427, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_get_table_k427, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_4)) {
      u64 _t_1 = task_node(e, FID_wire_get_list_4, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_4, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_table_k427)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_cvar_get_table_k428;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_cvar_get_table_k428, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_cvar_get_table_k428, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_3)) {
        u64 _t_3 = task_node(e, FID_wire_get_list_3, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_list_3, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_list_3);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_get_table_k428)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[5];
    if (spin_89(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_step)
    u32 _st_0 = r0;
    Term _st_1 = r1;
    Term _st_2 = r2;
    Term _input_0 = r3;
    WL_OPEN
    if (_st_0 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _st_1;
        STK(1) = _st_2;
        STK(2) = FID_ffi_cvar_step_k433;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_cvar_step_k433, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _st_1;
        e.mem[_t_0 + 1] = _st_2;
        WL_CONT = term_tsk(FID_ffi_cvar_step_k433, _t_0);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else {
      term_sink(e, _input_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = term_ctr(CID_SCon, STAT_OFF + 630);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_step_k433)
    WL_POPN(2);
    Term _st_3 = STK(0);
    Term _st_4 = STK(1);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (term_aux(_h_2) == CID_SNil) {
        _st_3 = term_keep(e, _st_3, 1);
        _st_4 = term_keep(e, _st_4, 1);
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _st_3;
          STK(1) = _st_4;
          STK(2) = FID_ffi_cvar_step_k434;
          WL_PUSHN(3);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_cvar_step_k434, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _st_3;
          e.mem[_t_2 + 1] = _st_4;
          WL_CONT = term_tsk(FID_ffi_cvar_step_k434, _t_2);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_cvar_press)) {
          u64 _t_3 = task_node(e, FID_cvar_press, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _st_3;
          e.mem[_t_3 + 1] = _h_1;
          e.mem[_t_3 + 2] = _st_4;
          return term_tsk(FID_cvar_press, _t_3);
        }
        r0 = _st_3;
        r1 = _h_1;
        r2 = _st_4;
        WL_JMP(FID_cvar_press);
      } else {
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _h_2, 2, _fb_0);
        u32 _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        term_sink(e, _f_1);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 0;
        r1 = _st_3;
        r2 = _st_4;
        r3 = term_ctr(CID_SCon, STAT_OFF + 298);
        WL_RETN(4);
      }
    } else {
      r0 = 0;
      r1 = _st_3;
      r2 = _st_4;
      r3 = term_ctr(CID_SCon, STAT_OFF + 340);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_step_k434)
    WL_POPN(2);
    Term _st_5 = STK(0);
    Term _st_6 = STK(1);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _st_5;
      STK(1) = _st_6;
      STK(2) = FID_ffi_cvar_step_k435;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_cvar_step_k435, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _st_5;
      e.mem[_t_4 + 1] = _st_6;
      WL_CONT = term_tsk(FID_ffi_cvar_step_k435, _t_4);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_put_exp)) {
      u64 _t_5 = task_node(e, FID_ffi_cvar_put_exp, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _h_3;
      e.mem[_t_5 + 1] = _h_4;
      e.mem[_t_5 + 2] = term_pak(CID_SNil, 0);
      return term_tsk(FID_ffi_cvar_put_exp, _t_5);
    }
    r0 = _h_3;
    r1 = _h_4;
    r2 = term_pak(CID_SNil, 0);
    WL_JMP(FID_ffi_cvar_put_exp);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_step_k435)
    WL_POPN(2);
    Term _st_7 = STK(0);
    Term _st_8 = STK(1);
    Term _h_5 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _st_7;
    r2 = _st_8;
    r3 = _h_5;
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step)
    u32 _s_0 = r0;
    Term _s_1 = r1;
    Term _s_2 = r2;
    Term _input_0 = r3;
    WL_OPEN
    if (_s_0 == 0) {
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _s_1;
        STK(1) = _s_2;
        STK(2) = _input_0;
        STK(3) = FID_ffi_echo_step_k438;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_echo_step_k438, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _s_1;
        e.mem[_t_0 + 1] = _s_2;
        e.mem[_t_0 + 2] = _input_0;
        WL_CONT = term_tsk(FID_ffi_echo_step_k438, _t_0);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_Nat_show)) {
        u64 _t_1 = task_node(e, FID_Nat_show, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = nat_chk(e, _s_1 + 1ull);
        return term_tsk(FID_Nat_show, _t_1);
      }
      r0 = nat_chk(e, _s_1 + 1ull);
      WL_JMP(FID_Nat_show);
    } else {
      term_sink(e, _input_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = term_ctr(CID_SCon, STAT_OFF + 664);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k438)
    WL_POPN(3);
    Term _s_3 = STK(0);
    Term _s_4 = STK(1);
    Term _input_1 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _s_3;
      STK(1) = _input_1;
      STK(2) = _h_0;
      STK(3) = FID_ffi_echo_step_k439;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_ffi_echo_step_k439, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _s_3;
      e.mem[_t_2 + 1] = _input_1;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_ffi_echo_step_k439, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_String_append)) {
      u64 _t_3 = task_node(e, FID_String_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = term_ctr(CID_SCon, STAT_OFF + 632);
      e.mem[_t_3 + 1] = _s_4;
      return term_tsk(FID_String_append, _t_3);
    }
    r0 = term_ctr(CID_SCon, STAT_OFF + 632);
    r1 = _s_4;
    WL_JMP(FID_String_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k439)
    WL_POPN(3);
    Term _s_5 = STK(0);
    Term _input_2 = STK(1);
    Term _h_2 = STK(2);
    Term _h_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _s_5;
      STK(1) = _input_2;
      STK(2) = FID_ffi_echo_step_k440;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_echo_step_k440, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _s_5;
      e.mem[_t_4 + 1] = _input_2;
      WL_CONT = term_tsk(FID_ffi_echo_step_k440, _t_4);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_String_append)) {
      u64 _t_5 = task_node(e, FID_String_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _h_2;
      e.mem[_t_5 + 1] = _h_1;
      return term_tsk(FID_String_append, _t_5);
    }
    r0 = _h_2;
    r1 = _h_1;
    WL_JMP(FID_String_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k440)
    WL_POPN(2);
    Term _s_6 = STK(0);
    Term _input_3 = STK(1);
    Term _h_3 = r0;
    WL_OPEN
    r0 = 0;
    r1 = nat_chk(e, _s_6 + 1ull);
    r2 = _input_3;
    r3 = _h_3;
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_open)
    Term _input_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_cvar_open_k462;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_cvar_open_k462, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_cvar_open_k462, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_table)) {
      u64 _t_1 = task_node(e, FID_ffi_cvar_get_table, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _input_0;
      return term_tsk(FID_ffi_cvar_get_table, _t_1);
    }
    r0 = _input_0;
    WL_JMP(FID_ffi_cvar_get_table);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_cvar_open_k462)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    WL_OPEN
    Term _o_2[4];
    if (spin_92(e, _o_2, _h_0, _h_1, _h_2, _h_3, _h_4) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = _o_2[1];
    r2 = _o_2[2];
    r3 = _o_2[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_open)
    Term _input_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_echo_open_k466;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_echo_open_k466, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_echo_open_k466, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_U32_read)) {
      u64 _t_1 = task_node(e, FID_U32_read, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _input_0;
      return term_tsk(FID_U32_read, _t_1);
    }
    r0 = _input_0;
    WL_JMP(FID_U32_read);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_open_k466)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    if (_h_0 == 1) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_echo_open_k467;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_echo_open_k467, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_echo_open_k467, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_U32_show)) {
        u64 _t_3 = task_node(e, FID_U32_show, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_1;
        return term_tsk(FID_U32_show, _t_3);
      }
      r0 = _h_1;
      WL_JMP(FID_U32_show);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = term_ctr(CID_SCon, STAT_OFF + 560);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_open_k467)
    WL_POPN(1);
    u32 _h_3 = STK(0);
    Term _h_2 = r0;
    WL_OPEN
    r0 = 0;
    r1 = ((u64)_h_3);
    r2 = term_pak(CID_SNil, 0);
    r3 = _h_2;
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_go)
    u32 _state_0 = r0;
    u32 _state_1 = r1;
    Term _state_2 = r2;
    Term _state_3 = r3;
    Term _input_0 = r4;
    WL_OPEN
    if (_state_0 == 0) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_step_go_k470;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_step_go_k470, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_step_go_k470, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_echo_step)) {
        u64 _t_1 = task_node(e, FID_ffi_echo_step, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _state_1;
        e.mem[_t_1 + 1] = _state_2;
        e.mem[_t_1 + 2] = _state_3;
        e.mem[_t_1 + 3] = _input_0;
        return term_tsk(FID_ffi_echo_step, _t_1);
      }
      r0 = _state_1;
      r1 = _state_2;
      r2 = _state_3;
      r3 = _input_0;
      WL_JMP(FID_ffi_echo_step);
    } else if (_state_0 == 1) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_step_go_k471;
        WL_PUSHN(1);
      } else {
        u64 _t_2 = task_node(e, FID_step_go_k471, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_step_go_k471, _t_2);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_step)) {
        u64 _t_3 = task_node(e, FID_ffi_cvar_step, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _state_1;
        e.mem[_t_3 + 1] = _state_2;
        e.mem[_t_3 + 2] = _state_3;
        e.mem[_t_3 + 3] = _input_0;
        return term_tsk(FID_ffi_cvar_step, _t_3);
      }
      r0 = _state_1;
      r1 = _state_2;
      r2 = _state_3;
      r3 = _input_0;
      WL_JMP(FID_ffi_cvar_step);
    } else {
      term_sink(e, _input_0);
      r0 = 2;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = term_ctr(CID_SCon, STAT_OFF + 692);
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_go_k470)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_93(e, _o_0, _h_0, _h_1, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_go_k471)
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    Term _h_7 = r3;
    WL_OPEN
    Term _o_1[5];
    if (spin_94(e, _o_1, _h_4, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go)
    u32 _entry_0 = r0;
    Term _input_0 = r1;
    WL_OPEN
    if (_entry_0 == 0) {
      Term _o_0[1];
      if (spin_95(e, _o_0, _input_0) == 0) {
        return 0;
      }
      r0 = _o_0[0];
      WL_RETN(1);
    } else if ((_entry_0 & 7) == 0) {
      u32 _14_0 = ((_entry_0 >> 3) & 1);
      u32 _15_0 = ((_entry_0 >> 4) & 1);
      u32 _15_1 = ((_entry_0 >> 5) & 1);
      u32 _15_2 = ((_entry_0 >> 6) & 1);
      u32 _15_3 = ((_entry_0 >> 7) & 1);
      u32 _15_4 = ((_entry_0 >> 8) & 1);
      u32 _15_5 = ((_entry_0 >> 9) & 1);
      u32 _15_6 = ((_entry_0 >> 10) & 1);
      u32 _15_7 = ((_entry_0 >> 11) & 1);
      u32 _15_8 = ((_entry_0 >> 12) & 1);
      u32 _15_9 = ((_entry_0 >> 13) & 1);
      u32 _15_10 = ((_entry_0 >> 14) & 1);
      u32 _15_11 = ((_entry_0 >> 15) & 1);
      u32 _15_12 = ((_entry_0 >> 16) & 1);
      u32 _15_13 = ((_entry_0 >> 17) & 1);
      u32 _15_14 = ((_entry_0 >> 18) & 1);
      u32 _15_15 = ((_entry_0 >> 19) & 1);
      u32 _15_16 = ((_entry_0 >> 20) & 1);
      u32 _15_17 = ((_entry_0 >> 21) & 1);
      u32 _15_18 = ((_entry_0 >> 22) & 1);
      u32 _15_19 = ((_entry_0 >> 23) & 1);
      u32 _15_20 = ((_entry_0 >> 24) & 1);
      u32 _15_21 = ((_entry_0 >> 25) & 1);
      u32 _15_22 = ((_entry_0 >> 26) & 1);
      u32 _15_23 = ((_entry_0 >> 27) & 1);
      u32 _15_24 = ((_entry_0 >> 28) & 1);
      u32 _15_25 = ((_entry_0 >> 29) & 1);
      u32 _15_26 = ((_entry_0 >> 30) & 1);
      u32 _15_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_1[1];
      if (spin_65(e, _o_1, term_ctr(CID_SCon, STAT_OFF + 688)) == 0) {
        return 0;
      }
      r0 = _o_1[0];
      WL_RETN(1);
    } else if (_entry_0 == 4) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k474;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_go_k474, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k474, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_director_get_req)) {
        u64 _t_1 = task_node(e, FID_ffi_director_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_ffi_director_get_req, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_director_get_req);
    } else if ((_entry_0 & 7) == 4) {
      u32 _72_0 = ((_entry_0 >> 3) & 1);
      u32 _73_0 = ((_entry_0 >> 4) & 1);
      u32 _73_1 = ((_entry_0 >> 5) & 1);
      u32 _73_2 = ((_entry_0 >> 6) & 1);
      u32 _73_3 = ((_entry_0 >> 7) & 1);
      u32 _73_4 = ((_entry_0 >> 8) & 1);
      u32 _73_5 = ((_entry_0 >> 9) & 1);
      u32 _73_6 = ((_entry_0 >> 10) & 1);
      u32 _73_7 = ((_entry_0 >> 11) & 1);
      u32 _73_8 = ((_entry_0 >> 12) & 1);
      u32 _73_9 = ((_entry_0 >> 13) & 1);
      u32 _73_10 = ((_entry_0 >> 14) & 1);
      u32 _73_11 = ((_entry_0 >> 15) & 1);
      u32 _73_12 = ((_entry_0 >> 16) & 1);
      u32 _73_13 = ((_entry_0 >> 17) & 1);
      u32 _73_14 = ((_entry_0 >> 18) & 1);
      u32 _73_15 = ((_entry_0 >> 19) & 1);
      u32 _73_16 = ((_entry_0 >> 20) & 1);
      u32 _73_17 = ((_entry_0 >> 21) & 1);
      u32 _73_18 = ((_entry_0 >> 22) & 1);
      u32 _73_19 = ((_entry_0 >> 23) & 1);
      u32 _73_20 = ((_entry_0 >> 24) & 1);
      u32 _73_21 = ((_entry_0 >> 25) & 1);
      u32 _73_22 = ((_entry_0 >> 26) & 1);
      u32 _73_23 = ((_entry_0 >> 27) & 1);
      u32 _73_24 = ((_entry_0 >> 28) & 1);
      u32 _73_25 = ((_entry_0 >> 29) & 1);
      u32 _73_26 = ((_entry_0 >> 30) & 1);
      u32 _73_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_7[1];
      if (spin_65(e, _o_7, term_ctr(CID_SCon, STAT_OFF + 688)) == 0) {
        return 0;
      }
      r0 = _o_7[0];
      WL_RETN(1);
    } else if (_entry_0 == 2) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k477;
        WL_PUSHN(1);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_go_k477, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k477, _t_6);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_child_env_get_req)) {
        u64 _t_7 = task_node(e, FID_ffi_child_env_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _input_0;
        return term_tsk(FID_ffi_child_env_get_req, _t_7);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_child_env_get_req);
    } else if ((_entry_0 & 3) == 2) {
      u32 _130_0 = ((_entry_0 >> 2) & 1);
      u32 _131_0 = ((_entry_0 >> 3) & 1);
      u32 _131_1 = ((_entry_0 >> 4) & 1);
      u32 _131_2 = ((_entry_0 >> 5) & 1);
      u32 _131_3 = ((_entry_0 >> 6) & 1);
      u32 _131_4 = ((_entry_0 >> 7) & 1);
      u32 _131_5 = ((_entry_0 >> 8) & 1);
      u32 _131_6 = ((_entry_0 >> 9) & 1);
      u32 _131_7 = ((_entry_0 >> 10) & 1);
      u32 _131_8 = ((_entry_0 >> 11) & 1);
      u32 _131_9 = ((_entry_0 >> 12) & 1);
      u32 _131_10 = ((_entry_0 >> 13) & 1);
      u32 _131_11 = ((_entry_0 >> 14) & 1);
      u32 _131_12 = ((_entry_0 >> 15) & 1);
      u32 _131_13 = ((_entry_0 >> 16) & 1);
      u32 _131_14 = ((_entry_0 >> 17) & 1);
      u32 _131_15 = ((_entry_0 >> 18) & 1);
      u32 _131_16 = ((_entry_0 >> 19) & 1);
      u32 _131_17 = ((_entry_0 >> 20) & 1);
      u32 _131_18 = ((_entry_0 >> 21) & 1);
      u32 _131_19 = ((_entry_0 >> 22) & 1);
      u32 _131_20 = ((_entry_0 >> 23) & 1);
      u32 _131_21 = ((_entry_0 >> 24) & 1);
      u32 _131_22 = ((_entry_0 >> 25) & 1);
      u32 _131_23 = ((_entry_0 >> 26) & 1);
      u32 _131_24 = ((_entry_0 >> 27) & 1);
      u32 _131_25 = ((_entry_0 >> 28) & 1);
      u32 _131_26 = ((_entry_0 >> 29) & 1);
      u32 _131_27 = ((_entry_0 >> 30) & 1);
      u32 _131_28 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_12[1];
      if (spin_65(e, _o_12, term_ctr(CID_SCon, STAT_OFF + 688)) == 0) {
        return 0;
      }
      r0 = _o_12[0];
      WL_RETN(1);
    } else if (_entry_0 == 1) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k480;
        WL_PUSHN(1);
      } else {
        u64 _t_12 = task_node(e, FID_ffi_go_k480, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k480, _t_12);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_13 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_13 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_13);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else if ((_entry_0 & 3) == 1) {
      u32 _192_0 = ((_entry_0 >> 2) & 1);
      u32 _193_0 = ((_entry_0 >> 3) & 1);
      u32 _193_1 = ((_entry_0 >> 4) & 1);
      u32 _193_2 = ((_entry_0 >> 5) & 1);
      u32 _193_3 = ((_entry_0 >> 6) & 1);
      u32 _193_4 = ((_entry_0 >> 7) & 1);
      u32 _193_5 = ((_entry_0 >> 8) & 1);
      u32 _193_6 = ((_entry_0 >> 9) & 1);
      u32 _193_7 = ((_entry_0 >> 10) & 1);
      u32 _193_8 = ((_entry_0 >> 11) & 1);
      u32 _193_9 = ((_entry_0 >> 12) & 1);
      u32 _193_10 = ((_entry_0 >> 13) & 1);
      u32 _193_11 = ((_entry_0 >> 14) & 1);
      u32 _193_12 = ((_entry_0 >> 15) & 1);
      u32 _193_13 = ((_entry_0 >> 16) & 1);
      u32 _193_14 = ((_entry_0 >> 17) & 1);
      u32 _193_15 = ((_entry_0 >> 18) & 1);
      u32 _193_16 = ((_entry_0 >> 19) & 1);
      u32 _193_17 = ((_entry_0 >> 20) & 1);
      u32 _193_18 = ((_entry_0 >> 21) & 1);
      u32 _193_19 = ((_entry_0 >> 22) & 1);
      u32 _193_20 = ((_entry_0 >> 23) & 1);
      u32 _193_21 = ((_entry_0 >> 24) & 1);
      u32 _193_22 = ((_entry_0 >> 25) & 1);
      u32 _193_23 = ((_entry_0 >> 26) & 1);
      u32 _193_24 = ((_entry_0 >> 27) & 1);
      u32 _193_25 = ((_entry_0 >> 28) & 1);
      u32 _193_26 = ((_entry_0 >> 29) & 1);
      u32 _193_27 = ((_entry_0 >> 30) & 1);
      u32 _193_28 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_23[1];
      if (spin_65(e, _o_23, term_ctr(CID_SCon, STAT_OFF + 688)) == 0) {
        return 0;
      }
      r0 = _o_23[0];
      WL_RETN(1);
    } else if (_entry_0 == 3) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k486;
        WL_PUSHN(1);
      } else {
        u64 _t_24 = task_node(e, FID_ffi_go_k486, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k486, _t_24);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_get_xreq)) {
        u64 _t_25 = task_node(e, FID_ffi_cvar_get_xreq, WL_CONT, WL_IDX, 0);
        e.mem[_t_25 + 0] = _input_0;
        return term_tsk(FID_ffi_cvar_get_xreq, _t_25);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_cvar_get_xreq);
    } else {
      u32 _252_0 = ((_entry_0 >> 2) & 1);
      u32 _253_0 = ((_entry_0 >> 3) & 1);
      u32 _253_1 = ((_entry_0 >> 4) & 1);
      u32 _253_2 = ((_entry_0 >> 5) & 1);
      u32 _253_3 = ((_entry_0 >> 6) & 1);
      u32 _253_4 = ((_entry_0 >> 7) & 1);
      u32 _253_5 = ((_entry_0 >> 8) & 1);
      u32 _253_6 = ((_entry_0 >> 9) & 1);
      u32 _253_7 = ((_entry_0 >> 10) & 1);
      u32 _253_8 = ((_entry_0 >> 11) & 1);
      u32 _253_9 = ((_entry_0 >> 12) & 1);
      u32 _253_10 = ((_entry_0 >> 13) & 1);
      u32 _253_11 = ((_entry_0 >> 14) & 1);
      u32 _253_12 = ((_entry_0 >> 15) & 1);
      u32 _253_13 = ((_entry_0 >> 16) & 1);
      u32 _253_14 = ((_entry_0 >> 17) & 1);
      u32 _253_15 = ((_entry_0 >> 18) & 1);
      u32 _253_16 = ((_entry_0 >> 19) & 1);
      u32 _253_17 = ((_entry_0 >> 20) & 1);
      u32 _253_18 = ((_entry_0 >> 21) & 1);
      u32 _253_19 = ((_entry_0 >> 22) & 1);
      u32 _253_20 = ((_entry_0 >> 23) & 1);
      u32 _253_21 = ((_entry_0 >> 24) & 1);
      u32 _253_22 = ((_entry_0 >> 25) & 1);
      u32 _253_23 = ((_entry_0 >> 26) & 1);
      u32 _253_24 = ((_entry_0 >> 27) & 1);
      u32 _253_25 = ((_entry_0 >> 28) & 1);
      u32 _253_26 = ((_entry_0 >> 29) & 1);
      u32 _253_27 = ((_entry_0 >> 30) & 1);
      u32 _253_28 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_27[1];
      if (spin_65(e, _o_27, term_ctr(CID_SCon, STAT_OFF + 688)) == 0) {
        return 0;
      }
      r0 = _o_27[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k474)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    u32 _h_4 = r4;
    u32 _h_5 = r5;
    Term _h_6 = r6;
    Term _h_7 = r7;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_2[1];
      if (spin_90(e, _o_2, _h_7) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_2[0];
      if (_v_0 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k475;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_go_k475, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k475, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_director_tick)) {
          u64 _t_3 = task_node(e, FID_director_tick, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_1;
          e.mem[_t_3 + 1] = _h_2;
          e.mem[_t_3 + 2] = _h_3;
          e.mem[_t_3 + 3] = _h_4;
          e.mem[_t_3 + 4] = _h_5;
          e.mem[_t_3 + 5] = _h_6;
          return term_tsk(FID_director_tick, _t_3);
        }
        r0 = _h_1;
        r1 = _h_2;
        r2 = _h_3;
        r3 = _h_4;
        r4 = _h_5;
        r5 = _h_6;
        WL_JMP(FID_director_tick);
      } else {
        term_sink(e, _h_3);
        term_sink(e, _h_6);
        Term _o_5[1];
        if (spin_65(e, _o_5, term_ctr(CID_SCon, STAT_OFF + 294)) == 0) {
          return 0;
        }
        r0 = _o_5[0];
        WL_RETN(1);
      }
    } else {
      Term _o_6[1];
      if (spin_65(e, _o_6, term_ctr(CID_SCon, STAT_OFF + 438)) == 0) {
        return 0;
      }
      r0 = _o_6[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k475)
    Term _h_8 = r0;
    Term _h_9 = r1;
    u32 _h_10 = r2;
    u32 _h_11 = r3;
    WL_OPEN
    Term _rest_0 = term_pak(CID_SNil, 0);
    Term _v_1 = 0;
    Term _o_3[1];
    if (spin_78(e, _o_3, _h_10, _h_11, _rest_0) == 0) {
      return 0;
    }
    _v_1 = _o_3[0];
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_8;
      STK(1) = FID_ffi_go_k476;
      WL_PUSHN(2);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_go_k476, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _h_8;
      WL_CONT = term_tsk(FID_ffi_go_k476, _t_4);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_5)) {
      u64 _t_5 = task_node(e, FID_wire_put_list_5, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _h_9;
      e.mem[_t_5 + 1] = _v_1;
      return term_tsk(FID_wire_put_list_5, _t_5);
    }
    r0 = _h_9;
    r1 = _v_1;
    WL_JMP(FID_wire_put_list_5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k476)
    WL_POPN(1);
    Term _h_13 = STK(0);
    Term _h_12 = r0;
    WL_OPEN
    Term _o_4[1];
    if (spin_10(e, _o_4, _h_13, _h_12) == 0) {
      return 0;
    }
    r0 = _o_4[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k477)
    u32 _h_14 = r0;
    Term _h_15 = r1;
    Term _h_16 = r2;
    Term _h_17 = r3;
    Term _h_18 = r4;
    Term _h_19 = r5;
    WL_OPEN
    if (_h_14 == 0) {
      u32 _v_2 = 0;
      Term _o_8[1];
      if (spin_90(e, _o_8, _h_19) == 0) {
        return 0;
      }
      _v_2 = (u32)_o_8[0];
      if (_v_2 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k478;
          WL_PUSHN(1);
        } else {
          u64 _t_8 = task_node(e, FID_ffi_go_k478, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k478, _t_8);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_child_env_child)) {
          u64 _t_9 = task_node(e, FID_child_env_child, WL_CONT, WL_IDX, 0);
          e.mem[_t_9 + 0] = _h_15;
          e.mem[_t_9 + 1] = _h_16;
          e.mem[_t_9 + 2] = _h_17;
          e.mem[_t_9 + 3] = _h_18;
          return term_tsk(FID_child_env_child, _t_9);
        }
        r0 = _h_15;
        r1 = _h_16;
        r2 = _h_17;
        r3 = _h_18;
        WL_JMP(FID_child_env_child);
      } else {
        term_sink(e, _h_15);
        term_sink(e, _h_16);
        term_sink(e, _h_17);
        term_sink(e, _h_18);
        Term _o_10[1];
        if (spin_65(e, _o_10, term_ctr(CID_SCon, STAT_OFF + 280)) == 0) {
          return 0;
        }
        r0 = _o_10[0];
        WL_RETN(1);
      }
    } else {
      Term _o_11[1];
      if (spin_65(e, _o_11, term_ctr(CID_SCon, STAT_OFF + 422)) == 0) {
        return 0;
      }
      r0 = _o_11[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k478)
    Term _h_20 = r0;
    WL_OPEN
    Term _rest_1 = term_pak(CID_SNil, 0);
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_go_k479;
      WL_PUSHN(1);
    } else {
      u64 _t_10 = task_node(e, FID_ffi_go_k479, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_go_k479, _t_10);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_1)) {
      u64 _t_11 = task_node(e, FID_wire_put_list_go_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_11 + 0] = _h_20;
      e.mem[_t_11 + 1] = _rest_1;
      return term_tsk(FID_wire_put_list_go_1, _t_11);
    }
    r0 = _h_20;
    r1 = _rest_1;
    WL_JMP(FID_wire_put_list_go_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k479)
    Term _h_21 = r0;
    Term _h_22 = r1;
    WL_OPEN
    Term _o_9[1];
    if (spin_52(e, _o_9, _h_21, _h_22) == 0) {
      return 0;
    }
    r0 = _o_9[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k480)
    u32 _h_23 = r0;
    Term _h_24 = r1;
    Term _h_25 = r2;
    WL_OPEN
    if (_h_23 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_24;
        STK(1) = FID_ffi_go_k481;
        WL_PUSHN(2);
      } else {
        u64 _t_14 = task_node(e, FID_ffi_go_k481, WL_CONT, WL_IDX, 1);
        e.mem[_t_14 + 0] = _h_24;
        WL_CONT = term_tsk(FID_ffi_go_k481, _t_14);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_u32)) {
        u64 _t_15 = task_node(e, FID_wire_get_u32, WL_CONT, WL_IDX, 0);
        e.mem[_t_15 + 0] = _h_25;
        return term_tsk(FID_wire_get_u32, _t_15);
      }
      r0 = _h_25;
      WL_JMP(FID_wire_get_u32);
    } else {
      Term _o_22[1];
      if (spin_64(e, _o_22) == 0) {
        return 0;
      }
      r0 = _o_22[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k481)
    WL_POPN(1);
    Term _h_29 = STK(0);
    u32 _h_26 = r0;
    u32 _h_27 = r1;
    Term _h_28 = r2;
    WL_OPEN
    if (_h_26 == 0) {
      u32 _v_3 = 0;
      u32 _v_4 = 0;
      Term _v_5 = 0;
      Term _o_13[3];
      if (spin_1(e, _o_13, _h_28) == 0) {
        return 0;
      }
      _v_3 = (u32)_o_13[0];
      _v_4 = (u32)_o_13[1];
      _v_5 = _o_13[2];
      if (_v_3 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _v_4;
          STK(1) = _h_29;
          STK(2) = _h_27;
          STK(3) = FID_ffi_go_k482;
          WL_PUSHN(4);
        } else {
          u64 _t_16 = task_node(e, FID_ffi_go_k482, WL_CONT, WL_IDX, 1);
          e.mem[_t_16 + 0] = _v_4;
          e.mem[_t_16 + 1] = _h_29;
          e.mem[_t_16 + 2] = _h_27;
          WL_CONT = term_tsk(FID_ffi_go_k482, _t_16);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
          u64 _t_17 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
          e.mem[_t_17 + 0] = _v_5;
          return term_tsk(FID_wire_get_str, _t_17);
        }
        r0 = _v_5;
        WL_JMP(FID_wire_get_str);
      } else {
        Term _o_20[1];
        if (spin_64(e, _o_20) == 0) {
          return 0;
        }
        r0 = _o_20[0];
        WL_RETN(1);
      }
    } else {
      Term _o_21[1];
      if (spin_64(e, _o_21) == 0) {
        return 0;
      }
      r0 = _o_21[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k482)
    WL_POPN(3);
    u32 _v_6 = STK(0);
    Term _h_33 = STK(1);
    u32 _h_34 = STK(2);
    u32 _h_30 = r0;
    Term _h_31 = r1;
    Term _h_32 = r2;
    WL_OPEN
    if (_h_30 == 0) {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _h_31;
        STK(1) = _h_33;
        STK(2) = _h_34;
        STK(3) = _v_6;
        STK(4) = FID_ffi_go_k483;
        WL_PUSHN(5);
      } else {
        u64 _t_18 = task_node(e, FID_ffi_go_k483, WL_CONT, WL_IDX, 1);
        e.mem[_t_18 + 0] = _h_31;
        e.mem[_t_18 + 1] = _h_33;
        e.mem[_t_18 + 2] = _h_34;
        e.mem[_t_18 + 3] = _v_6;
        WL_CONT = term_tsk(FID_ffi_go_k483, _t_18);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_7)) {
        u64 _t_19 = task_node(e, FID_wire_get_list_7, WL_CONT, WL_IDX, 0);
        e.mem[_t_19 + 0] = _h_32;
        return term_tsk(FID_wire_get_list_7, _t_19);
      }
      r0 = _h_32;
      WL_JMP(FID_wire_get_list_7);
    } else {
      Term _o_19[1];
      if (spin_64(e, _o_19) == 0) {
        return 0;
      }
      r0 = _o_19[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k483)
    WL_POPN(4);
    Term _h_38 = STK(0);
    Term _h_39 = STK(1);
    u32 _h_40 = STK(2);
    u32 _v_7 = STK(3);
    u32 _h_35 = r0;
    Term _h_36 = r1;
    Term _h_37 = r2;
    WL_OPEN
    if (_h_35 == 0) {
      if (term_aux(_h_37) == CID_SNil) {
        if (seq) {
          WL_ROOM(5, 0);
          STK(0) = _h_39;
          STK(1) = _h_40;
          STK(2) = _v_7;
          STK(3) = _h_38;
          STK(4) = FID_ffi_go_k484;
          WL_PUSHN(5);
        } else {
          u64 _t_20 = task_node(e, FID_ffi_go_k484, WL_CONT, WL_IDX, 1);
          e.mem[_t_20 + 0] = _h_39;
          e.mem[_t_20 + 1] = _h_40;
          e.mem[_t_20 + 2] = _v_7;
          e.mem[_t_20 + 3] = _h_38;
          WL_CONT = term_tsk(FID_ffi_go_k484, _t_20);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_7)) {
          u64 _t_21 = task_node(e, FID_wire_put_list_7, WL_CONT, WL_IDX, 0);
          e.mem[_t_21 + 0] = _h_36;
          e.mem[_t_21 + 1] = term_pak(CID_SNil, 0);
          return term_tsk(FID_wire_put_list_7, _t_21);
        }
        r0 = _h_36;
        r1 = term_pak(CID_SNil, 0);
        WL_JMP(FID_wire_put_list_7);
      } else {
        term_sink(e, _h_36);
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _h_37, 2, _fb_0);
        u32 _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        term_sink(e, _f_1);
        term_sink(e, _h_38);
        Term _o_17[1];
        if (spin_64(e, _o_17) == 0) {
          return 0;
        }
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _o_17[0];
        WL_RETN(1);
      }
    } else {
      term_sink(e, _h_38);
      Term _o_18[1];
      if (spin_64(e, _o_18) == 0) {
        return 0;
      }
      r0 = _o_18[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k484)
    WL_POPN(4);
    Term _h_42 = STK(0);
    u32 _h_43 = STK(1);
    u32 _v_8 = STK(2);
    Term _h_44 = STK(3);
    Term _h_41 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _h_42;
      STK(1) = _h_43;
      STK(2) = _v_8;
      STK(3) = FID_ffi_go_k485;
      WL_PUSHN(4);
    } else {
      u64 _t_22 = task_node(e, FID_ffi_go_k485, WL_CONT, WL_IDX, 1);
      e.mem[_t_22 + 0] = _h_42;
      e.mem[_t_22 + 1] = _h_43;
      e.mem[_t_22 + 2] = _v_8;
      WL_CONT = term_tsk(FID_ffi_go_k485, _t_22);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_str)) {
      u64 _t_23 = task_node(e, FID_wire_put_str, WL_CONT, WL_IDX, 0);
      e.mem[_t_23 + 0] = _h_44;
      e.mem[_t_23 + 1] = _h_41;
      return term_tsk(FID_wire_put_str, _t_23);
    }
    r0 = _h_44;
    r1 = _h_41;
    WL_JMP(FID_wire_put_str);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k485)
    WL_POPN(3);
    Term _h_46 = STK(0);
    u32 _h_47 = STK(1);
    u32 _v_9 = STK(2);
    Term _h_45 = r0;
    WL_OPEN
    Term _v_10 = 0;
    Term _v_11 = 0;
    Term _o_14[1];
    if (spin_17(e, _o_14, _v_9, _h_45) == 0) {
      return 0;
    }
    _v_11 = _o_14[0];
    Term _o_15[1];
    if (spin_63(e, _o_15, _h_47, _v_11) == 0) {
      return 0;
    }
    _v_10 = _o_15[0];
    Term _o_16[1];
    if (spin_10(e, _o_16, _h_46, _v_10) == 0) {
      return 0;
    }
    r0 = _o_16[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k486)
    u32 _h_48 = r0;
    Term _h_49 = r1;
    Term _h_50 = r2;
    Term _h_51 = r3;
    WL_OPEN
    if (_h_48 == 0) {
      u32 _v_12 = 0;
      Term _o_24[1];
      if (spin_90(e, _o_24, _h_51) == 0) {
        return 0;
      }
      _v_12 = (u32)_o_24[0];
      if (_v_12 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k487;
          WL_PUSHN(1);
        } else {
          u64 _t_26 = task_node(e, FID_ffi_go_k487, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k487, _t_26);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_cvar_expand)) {
          u64 _t_27 = task_node(e, FID_cvar_expand, WL_CONT, WL_IDX, 0);
          e.mem[_t_27 + 0] = _h_50;
          e.mem[_t_27 + 1] = _h_49;
          return term_tsk(FID_cvar_expand, _t_27);
        }
        r0 = _h_50;
        r1 = _h_49;
        WL_JMP(FID_cvar_expand);
      } else {
        term_sink(e, _h_49);
        term_sink(e, _h_50);
        Term _o_25[1];
        if (spin_65(e, _o_25, term_ctr(CID_SCon, STAT_OFF + 262)) == 0) {
          return 0;
        }
        r0 = _o_25[0];
        WL_RETN(1);
      }
    } else {
      Term _o_26[1];
      if (spin_65(e, _o_26, term_ctr(CID_SCon, STAT_OFF + 384)) == 0) {
        return 0;
      }
      r0 = _o_26[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k487)
    u32 _h_52 = r0;
    Term _h_53 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_put_exp)) {
      u64 _t_28 = task_node(e, FID_ffi_cvar_put_exp, WL_CONT, WL_IDX, 0);
      e.mem[_t_28 + 0] = _h_52;
      e.mem[_t_28 + 1] = _h_53;
      e.mem[_t_28 + 2] = term_pak(CID_SNil, 0);
      return term_tsk(FID_ffi_cvar_put_exp, _t_28);
    }
    r0 = _h_52;
    r1 = _h_53;
    r2 = term_pak(CID_SNil, 0);
    WL_JMP(FID_ffi_cvar_put_exp);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_go)
    u32 _entry_0 = r0;
    Term _input_0 = r1;
    WL_OPEN
    if (_entry_0 == 0) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_open_go_k491;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_open_go_k491, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_open_go_k491, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_echo_open)) {
        u64 _t_1 = task_node(e, FID_ffi_echo_open, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_ffi_echo_open, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_echo_open);
    } else if ((_entry_0 & 1) == 0) {
      u32 _11_0 = ((_entry_0 >> 1) & 1);
      u32 _12_0 = ((_entry_0 >> 2) & 1);
      u32 _12_1 = ((_entry_0 >> 3) & 1);
      u32 _12_2 = ((_entry_0 >> 4) & 1);
      u32 _12_3 = ((_entry_0 >> 5) & 1);
      u32 _12_4 = ((_entry_0 >> 6) & 1);
      u32 _12_5 = ((_entry_0 >> 7) & 1);
      u32 _12_6 = ((_entry_0 >> 8) & 1);
      u32 _12_7 = ((_entry_0 >> 9) & 1);
      u32 _12_8 = ((_entry_0 >> 10) & 1);
      u32 _12_9 = ((_entry_0 >> 11) & 1);
      u32 _12_10 = ((_entry_0 >> 12) & 1);
      u32 _12_11 = ((_entry_0 >> 13) & 1);
      u32 _12_12 = ((_entry_0 >> 14) & 1);
      u32 _12_13 = ((_entry_0 >> 15) & 1);
      u32 _12_14 = ((_entry_0 >> 16) & 1);
      u32 _12_15 = ((_entry_0 >> 17) & 1);
      u32 _12_16 = ((_entry_0 >> 18) & 1);
      u32 _12_17 = ((_entry_0 >> 19) & 1);
      u32 _12_18 = ((_entry_0 >> 20) & 1);
      u32 _12_19 = ((_entry_0 >> 21) & 1);
      u32 _12_20 = ((_entry_0 >> 22) & 1);
      u32 _12_21 = ((_entry_0 >> 23) & 1);
      u32 _12_22 = ((_entry_0 >> 24) & 1);
      u32 _12_23 = ((_entry_0 >> 25) & 1);
      u32 _12_24 = ((_entry_0 >> 26) & 1);
      u32 _12_25 = ((_entry_0 >> 27) & 1);
      u32 _12_26 = ((_entry_0 >> 28) & 1);
      u32 _12_27 = ((_entry_0 >> 29) & 1);
      u32 _12_28 = ((_entry_0 >> 30) & 1);
      u32 _12_29 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      r0 = 2;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = term_ctr(CID_SCon, STAT_OFF + 692);
      WL_RETN(5);
    } else if (_entry_0 == 3) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_open_go_k492;
        WL_PUSHN(1);
      } else {
        u64 _t_2 = task_node(e, FID_open_go_k492, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_open_go_k492, _t_2);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_cvar_open)) {
        u64 _t_3 = task_node(e, FID_ffi_cvar_open, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _input_0;
        return term_tsk(FID_ffi_cvar_open, _t_3);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_cvar_open);
    } else {
      u32 _73_0 = ((_entry_0 >> 1) & 1);
      u32 _74_0 = ((_entry_0 >> 2) & 1);
      u32 _74_1 = ((_entry_0 >> 3) & 1);
      u32 _74_2 = ((_entry_0 >> 4) & 1);
      u32 _74_3 = ((_entry_0 >> 5) & 1);
      u32 _74_4 = ((_entry_0 >> 6) & 1);
      u32 _74_5 = ((_entry_0 >> 7) & 1);
      u32 _74_6 = ((_entry_0 >> 8) & 1);
      u32 _74_7 = ((_entry_0 >> 9) & 1);
      u32 _74_8 = ((_entry_0 >> 10) & 1);
      u32 _74_9 = ((_entry_0 >> 11) & 1);
      u32 _74_10 = ((_entry_0 >> 12) & 1);
      u32 _74_11 = ((_entry_0 >> 13) & 1);
      u32 _74_12 = ((_entry_0 >> 14) & 1);
      u32 _74_13 = ((_entry_0 >> 15) & 1);
      u32 _74_14 = ((_entry_0 >> 16) & 1);
      u32 _74_15 = ((_entry_0 >> 17) & 1);
      u32 _74_16 = ((_entry_0 >> 18) & 1);
      u32 _74_17 = ((_entry_0 >> 19) & 1);
      u32 _74_18 = ((_entry_0 >> 20) & 1);
      u32 _74_19 = ((_entry_0 >> 21) & 1);
      u32 _74_20 = ((_entry_0 >> 22) & 1);
      u32 _74_21 = ((_entry_0 >> 23) & 1);
      u32 _74_22 = ((_entry_0 >> 24) & 1);
      u32 _74_23 = ((_entry_0 >> 25) & 1);
      u32 _74_24 = ((_entry_0 >> 26) & 1);
      u32 _74_25 = ((_entry_0 >> 27) & 1);
      u32 _74_26 = ((_entry_0 >> 28) & 1);
      u32 _74_27 = ((_entry_0 >> 29) & 1);
      u32 _74_28 = ((_entry_0 >> 30) & 1);
      u32 _74_29 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      r0 = 2;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = term_ctr(CID_SCon, STAT_OFF + 692);
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_go_k491)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_96(e, _o_0, _h_0, _h_1, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_go_k492)
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    Term _h_7 = r3;
    WL_OPEN
    Term _o_1[5];
    if (spin_97(e, _o_1, _h_4, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step)
    u32 _state_0 = r0;
    u32 _state_1 = r1;
    Term _state_2 = r2;
    Term _state_3 = r3;
    Term _input_0 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_step_k494;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_step_k494, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_step_k494, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_step_go)) {
      u64 _t_1 = task_node(e, FID_step_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _state_0;
      e.mem[_t_1 + 1] = _state_1;
      e.mem[_t_1 + 2] = _state_2;
      e.mem[_t_1 + 3] = _state_3;
      e.mem[_t_1 + 4] = _input_0;
      return term_tsk(FID_step_go, _t_1);
    }
    r0 = _state_0;
    r1 = _state_1;
    r2 = _state_2;
    r3 = _state_3;
    r4 = _input_0;
    WL_JMP(FID_step_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_k494)
    u32 _r_0 = r0;
    u32 _r_1 = r1;
    Term _r_2 = r2;
    Term _r_3 = r3;
    Term _r_4 = r4;
    WL_OPEN
    r0 = _r_0;
    r1 = _r_1;
    r2 = _r_2;
    r3 = _r_3;
    r4 = _r_4;
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_close)
    u32 _state_0 = r0;
    u32 _state_1 = r1;
    Term _state_2 = r2;
    Term _state_3 = r3;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_98(e, _o_0, _state_0, _state_1, _state_2, _state_3) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    r0 = _v_0;
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi)
    u32 _entry_0 = r0;
    Term _input_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_k498;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_k498, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_k498, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_go)) {
      u64 _t_1 = task_node(e, FID_ffi_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _entry_0;
      e.mem[_t_1 + 1] = _input_0;
      return term_tsk(FID_ffi_go, _t_1);
    }
    r0 = _entry_0;
    r1 = _input_0;
    WL_JMP(FID_ffi_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_k498)
    Term _r_0 = r0;
    WL_OPEN
    r0 = _r_0;
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_U32_read_go)
    Term _s_0 = r0;
    u32 _acc_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_s_0) == CID_SNil) {
      r0 = 1;
      r1 = _acc_0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_0, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u32 _n_0 = U32_BIN(U32_BIN(_acc_0, *, 10ull), +, U32_BIN(_f_0, -, 48ull));
      Term _a_0 = 10ull;
      u32 _s_1 = U32_BIN(((u32)(_a_0) == 0 ? 0 : (u64)U32_QUO((u32)(_n_0), (u32)(_a_0))), ==, _acc_0);
      if (_s_1 == 1) {
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _n_0;
        _s_0 = r0;
        _acc_0 = r1;
        WL_AGAIN(FID_U32_read_go);
      } else {
        term_sink(e, _f_1);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 0;
        r1 = 0;
        WL_RETN(2);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open)
    u32 _entry_0 = r0;
    Term _input_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_open_k503;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_open_k503, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_open_k503, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_open_go)) {
      u64 _t_1 = task_node(e, FID_open_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _entry_0;
      e.mem[_t_1 + 1] = _input_0;
      return term_tsk(FID_open_go, _t_1);
    }
    r0 = _entry_0;
    r1 = _input_0;
    WL_JMP(FID_open_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_k503)
    u32 _r_0 = r0;
    u32 _r_1 = r1;
    Term _r_2 = r2;
    Term _r_3 = r3;
    Term _r_4 = r4;
    WL_OPEN
    r0 = _r_0;
    r1 = _r_1;
    r2 = _r_2;
    r3 = _r_3;
    r4 = _r_4;
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps)
    Term _events_0 = r0;
    u32 _r_0 = r1;
    u32 _r_1 = r2;
    Term _r_2 = r3;
    Term _r_3 = r4;
    Term _r_4 = r5;
    WL_OPEN
    if (term_aux(_events_0) == CID_Nil) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _r_4;
        STK(1) = FID_cli_steps_k505;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_cli_steps_k505, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _r_4;
        WL_CONT = term_tsk(FID_cli_steps_k505, _t_0);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_close)) {
        u64 _t_1 = task_node(e, FID_close, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _r_0;
        e.mem[_t_1 + 1] = _r_1;
        e.mem[_t_1 + 2] = _r_2;
        e.mem[_t_1 + 3] = _r_3;
        return term_tsk(FID_close, _t_1);
      }
      r0 = _r_0;
      r1 = _r_1;
      r2 = _r_2;
      r3 = _r_3;
      WL_JMP(FID_close);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _events_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_1;
        STK(1) = _r_4;
        STK(2) = FID_cli_steps_k506;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_cli_steps_k506, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _f_1;
        e.mem[_t_2 + 1] = _r_4;
        WL_CONT = term_tsk(FID_cli_steps_k506, _t_2);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_step)) {
        u64 _t_3 = task_node(e, FID_step, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _r_0;
        e.mem[_t_3 + 1] = _r_1;
        e.mem[_t_3 + 2] = _r_2;
        e.mem[_t_3 + 3] = _r_3;
        e.mem[_t_3 + 4] = _f_0;
        return term_tsk(FID_step, _t_3);
      }
      r0 = _r_0;
      r1 = _r_1;
      r2 = _r_2;
      r3 = _r_3;
      r4 = _f_0;
      WL_JMP(FID_step);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k505)
    WL_POPN(1);
    Term _r_5 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_99(e, _o_0, _r_5) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k506)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _r_6 = STK(1);
    u32 _h_1 = r0;
    u32 _h_2 = r1;
    Term _h_3 = r2;
    Term _h_4 = r3;
    Term _h_5 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _r_6;
      STK(1) = FID_cli_steps_k507;
      WL_PUSHN(2);
    } else {
      u64 _t_4 = task_node(e, FID_cli_steps_k507, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _r_6;
      WL_CONT = term_tsk(FID_cli_steps_k507, _t_4);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_cli_steps)) {
      u64 _t_5 = task_node(e, FID_cli_steps, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _f_2;
      e.mem[_t_5 + 1] = _h_1;
      e.mem[_t_5 + 2] = _h_2;
      e.mem[_t_5 + 3] = _h_3;
      e.mem[_t_5 + 4] = _h_4;
      e.mem[_t_5 + 5] = _h_5;
      return term_tsk(FID_cli_steps, _t_5);
    }
    r0 = _f_2;
    r1 = _h_1;
    r2 = _h_2;
    r3 = _h_3;
    r4 = _h_4;
    r5 = _h_5;
    WL_JMP(FID_cli_steps);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k507)
    WL_POPN(1);
    Term _r_7 = STK(0);
    Term _h_6 = r0;
    WL_OPEN
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _r_7);
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_6);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_U32_read)
    Term _s_0 = r0;
    WL_OPEN
    if (term_aux(_s_0) == CID_SNil) {
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_0, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u64 _nd_0 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _f_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _f_1);
      if (!DEVICE && !seq && fid_nofk(FID_U32_read_go)) {
        u64 _t_0 = task_node(e, FID_U32_read_go, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = term_ctr(CID_SCon, _nd_0);
        e.mem[_t_0 + 1] = 0ull;
        return term_tsk(FID_U32_read_go, _t_0);
      }
      r0 = term_ctr(CID_SCon, _nd_0);
      r1 = 0ull;
      WL_JMP(FID_U32_read_go);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print)
    Term _lines_0 = r0;
    WL_OPEN
    if (term_aux(_lines_0) == CID_Nil) {
      r0 = term_clo(FID_cli_print_c519, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _lines_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = _f_0;
      e.mem[_nd_0 + 1] = _f_1;
      spare_free(e, cls_fit(2), _sp_0);
      r0 = term_clo(FID_cli_print_c520, _nd_0);
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c519)
    Term _x_0 = r0;
    WL_OPEN
    Term _x_1 = term_pak(CID_Unit, 0);
    if (!DEVICE && !seq && fid_nofk(FID_Clo_apply)) {
      u64 _t_0 = task_node(e, FID_Clo_apply, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _x_0;
      e.mem[_t_0 + 1] = _x_1;
      return term_tsk(FID_Clo_apply, _t_0);
    }
    r0 = _x_0;
    r1 = _x_1;
    WL_JMP(FID_Clo_apply);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c520)
    Term _f_2 = r0;
    Term _f_3 = r1;
    Term _x_2 = r2;
    WL_OPEN
    u64 _nd_1 = heap_alloc(e, cls_fit(1));
    e.mem[_nd_1 + 0] = _f_2;
    u64 _nd_2 = heap_alloc(e, cls_fit(1));
    e.mem[_nd_2 + 0] = _f_3;
    if (!DEVICE && !seq && fid_nofk(FID_IO_bind)) {
      u64 _t_2 = task_node(e, FID_IO_bind, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = term_clo(FID_IO_print, _nd_1);
      e.mem[_t_2 + 1] = term_clo(FID_cli_print_c521, _nd_2);
      e.mem[_t_2 + 2] = _x_2;
      return term_tsk(FID_IO_bind, _t_2);
    }
    r0 = term_clo(FID_IO_print, _nd_1);
    r1 = term_clo(FID_cli_print_c521, _nd_2);
    r2 = _x_2;
    WL_JMP(FID_IO_bind);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c521)
    Term _f_4 = r0;
    Term _x_3 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_cli_print)) {
      u64 _t_1 = task_node(e, FID_cli_print, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _f_4;
      return term_tsk(FID_cli_print, _t_1);
    }
    r0 = _f_4;
    WL_JMP(FID_cli_print);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_args)
    Term _args_0 = r0;
    WL_OPEN
    if (term_aux(_args_0) == CID_Con) {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _args_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      term_sink(e, _f_0);
      if (term_aux(_f_1) == CID_Con) {
        Term _fb_1[2];
        u64 _sp_1 = ctr_take(e, _f_1, 2, _fb_1);
        Term _f_2 = _fb_1[0];
        Term _f_3 = _fb_1[1];
        if (term_aux(_f_3) == CID_Con) {
          Term _fb_2[2];
          u64 _sp_2 = ctr_take(e, _f_3, 2, _fb_2);
          Term _f_4 = _fb_2[0];
          Term _f_5 = _fb_2[1];
          if (term_aux(_f_5) == CID_Con) {
            Term _fb_3[2];
            u64 _sp_3 = ctr_take(e, _f_5, 2, _fb_3);
            Term _f_6 = _fb_3[0];
            Term _f_7 = _fb_3[1];
            spare_free(e, cls_fit(2), _sp_3);
            spare_free(e, cls_fit(2), _sp_2);
            spare_free(e, cls_fit(2), _sp_1);
            spare_free(e, cls_fit(2), _sp_0);
            if (seq) {
              WL_ROOM(4, 0);
              STK(0) = _f_2;
              STK(1) = _f_6;
              STK(2) = _f_7;
              STK(3) = FID_cli_args_k523;
              WL_PUSHN(4);
            } else {
              u64 _t_0 = task_node(e, FID_cli_args_k523, WL_CONT, WL_IDX, 1);
              e.mem[_t_0 + 0] = _f_2;
              e.mem[_t_0 + 1] = _f_6;
              e.mem[_t_0 + 2] = _f_7;
              WL_CONT = term_tsk(FID_cli_args_k523, _t_0);
              WL_IDX = 3;
            }
            if (!DEVICE && !seq && fid_nofk(FID_U32_read)) {
              u64 _t_1 = task_node(e, FID_U32_read, WL_CONT, WL_IDX, 0);
              e.mem[_t_1 + 0] = _f_4;
              return term_tsk(FID_U32_read, _t_1);
            }
            r0 = _f_4;
            WL_JMP(FID_U32_read);
          } else {
            term_sink(e, _f_2);
            term_sink(e, _f_4);
            spare_free(e, cls_fit(2), _sp_2);
            spare_free(e, cls_fit(2), _sp_1);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 0;
            r1 = 0;
            WL_RETN(2);
          }
        } else {
          term_sink(e, _f_2);
          spare_free(e, cls_fit(2), _sp_1);
          spare_free(e, cls_fit(2), _sp_0);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        }
      } else {
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 0;
        r1 = 0;
        WL_RETN(2);
      }
    } else {
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_args_k523)
    WL_POPN(3);
    Term _f_8 = STK(0);
    Term _f_9 = STK(1);
    Term _f_10 = STK(2);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    _f_8 = term_keep(e, _f_8, 1);
    Term _o_0[1];
    if (spin_21(e, _o_0, _f_8, term_ctr(CID_SCon, STAT_OFF + 700)) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    u32 _v_1 = 0;
    Term _o_1[1];
    if (spin_21(e, _o_1, _f_8, term_ctr(CID_SCon, STAT_OFF + 708)) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_1[0];
    if (_v_0 == 1) {
      if (_v_1 == 0) {
        if (_h_0 == 1) {
          if (term_aux(_f_10) == CID_Nil) {
            if (seq) {
              WL_ROOM(1, 0);
              STK(0) = FID_cli_args_k524;
              WL_PUSHN(1);
            } else {
              u64 _t_2 = task_node(e, FID_cli_args_k524, WL_CONT, WL_IDX, 1);
              WL_CONT = term_tsk(FID_cli_args_k524, _t_2);
              WL_IDX = 0;
            }
            if (!DEVICE && !seq && fid_nofk(FID_ffi)) {
              u64 _t_3 = task_node(e, FID_ffi, WL_CONT, WL_IDX, 0);
              e.mem[_t_3 + 0] = _h_1;
              e.mem[_t_3 + 1] = _f_9;
              return term_tsk(FID_ffi, _t_3);
            }
            r0 = _h_1;
            r1 = _f_9;
            WL_JMP(FID_ffi);
          } else {
            Term _fb_4[2];
            u64 _sp_4 = ctr_take(e, _f_10, 2, _fb_4);
            Term _f_11 = _fb_4[0];
            Term _f_12 = _fb_4[1];
            term_sink(e, _f_11);
            term_sink(e, _f_12);
            term_sink(e, _f_9);
            spare_free(e, cls_fit(2), _sp_4);
            r0 = 0;
            r1 = 0;
            WL_RETN(2);
          }
        } else {
          term_sink(e, _f_9);
          term_sink(e, _f_10);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        }
      } else {
        if (_h_0 == 1) {
          term_sink(e, _f_9);
          term_sink(e, _f_10);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        } else {
          term_sink(e, _f_9);
          term_sink(e, _f_10);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        }
      }
    } else {
      if (_v_1 == 1) {
        if (_h_0 == 1) {
          if (seq) {
            WL_ROOM(2, 0);
            STK(0) = _f_10;
            STK(1) = FID_cli_args_k525;
            WL_PUSHN(2);
          } else {
            u64 _t_4 = task_node(e, FID_cli_args_k525, WL_CONT, WL_IDX, 1);
            e.mem[_t_4 + 0] = _f_10;
            WL_CONT = term_tsk(FID_cli_args_k525, _t_4);
            WL_IDX = 1;
          }
          if (!DEVICE && !seq && fid_nofk(FID_open)) {
            u64 _t_5 = task_node(e, FID_open, WL_CONT, WL_IDX, 0);
            e.mem[_t_5 + 0] = _h_1;
            e.mem[_t_5 + 1] = _f_9;
            return term_tsk(FID_open, _t_5);
          }
          r0 = _h_1;
          r1 = _f_9;
          WL_JMP(FID_open);
        } else {
          term_sink(e, _f_9);
          term_sink(e, _f_10);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        }
      } else {
        if (_h_0 == 1) {
          term_sink(e, _f_9);
          term_sink(e, _f_10);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        } else {
          term_sink(e, _f_9);
          term_sink(e, _f_10);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        }
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_args_k524)
    Term _h_2 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _h_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
    r0 = 1;
    r1 = term_ctr(CID_Con, _nd_0);
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_args_k525)
    WL_POPN(1);
    Term _f_13 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_cli_args_k526;
      WL_PUSHN(1);
    } else {
      u64 _t_6 = task_node(e, FID_cli_args_k526, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_cli_args_k526, _t_6);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_cli_steps)) {
      u64 _t_7 = task_node(e, FID_cli_steps, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _f_13;
      e.mem[_t_7 + 1] = _h_3;
      e.mem[_t_7 + 2] = _h_4;
      e.mem[_t_7 + 3] = _h_5;
      e.mem[_t_7 + 4] = _h_6;
      e.mem[_t_7 + 5] = _h_7;
      return term_tsk(FID_cli_steps, _t_7);
    }
    r0 = _f_13;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    WL_JMP(FID_cli_steps);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_args_k526)
    Term _h_8 = r0;
    WL_OPEN
    r0 = 1;
    r1 = _h_8;
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_bind)
    Term _m_0 = r0;
    Term _f_0 = r1;
    Term _k_0 = r2;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = _f_0;
    e.mem[_nd_0 + 1] = _k_0;
    if (!DEVICE && !seq && fid_nofk(FID_Clo_apply)) {
      u64 _t_3 = task_node(e, FID_Clo_apply, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_0;
      e.mem[_t_3 + 1] = term_clo(FID_IO_bind_c530, _nd_0);
      return term_tsk(FID_Clo_apply, _t_3);
    }
    r0 = _m_0;
    r1 = term_clo(FID_IO_bind_c530, _nd_0);
    WL_JMP(FID_Clo_apply);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_bind_c530)
    Term _f_1 = r0;
    Term _k_1 = r1;
    Term _x_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _k_1;
      STK(1) = FID_IO_bind_k531;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_IO_bind_k531, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _k_1;
      WL_CONT = term_tsk(FID_IO_bind_k531, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_Clo_apply)) {
      u64 _t_1 = task_node(e, FID_Clo_apply, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _f_1;
      e.mem[_t_1 + 1] = _x_0;
      return term_tsk(FID_Clo_apply, _t_1);
    }
    r0 = _f_1;
    r1 = _x_0;
    WL_JMP(FID_Clo_apply);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_bind_k531)
    WL_POPN(1);
    Term _k_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_Clo_apply)) {
      u64 _t_2 = task_node(e, FID_Clo_apply, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _h_0;
      e.mem[_t_2 + 1] = _k_2;
      return term_tsk(FID_Clo_apply, _t_2);
    }
    r0 = _h_0;
    r1 = _k_2;
    WL_JMP(FID_Clo_apply);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main)
    WL_OPEN
    r0 = term_clo(FID_main_c533, 0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c533)
    Term _x_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_IO_bind)) {
      u64 _t_3 = task_node(e, FID_IO_bind, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = term_clo(FID_IO_args, 0);
      e.mem[_t_3 + 1] = term_clo(FID_main_c534, 0);
      e.mem[_t_3 + 2] = _x_0;
      return term_tsk(FID_IO_bind, _t_3);
    }
    r0 = term_clo(FID_IO_args, 0);
    r1 = term_clo(FID_main_c534, 0);
    r2 = _x_0;
    WL_JMP(FID_IO_bind);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c534)
    Term _x_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_main_k535;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_main_k535, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_main_k535, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_cli_args)) {
      u64 _t_1 = task_node(e, FID_cli_args, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _x_1;
      return term_tsk(FID_cli_args, _t_1);
    }
    r0 = _x_1;
    WL_JMP(FID_cli_args);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_k535)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    if (_h_0 == 1) {
      if (!DEVICE && !seq && fid_nofk(FID_cli_print)) {
        u64 _t_2 = task_node(e, FID_cli_print, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = _h_1;
        return term_tsk(FID_cli_print, _t_2);
      }
      r0 = _h_1;
      WL_JMP(FID_cli_print);
    } else {
      r0 = term_clo(FID_main_c536, 0);
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c536)
    Term _x_2 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_100(e, _o_0, 2ull, term_ctr(CID_SCon, STAT_OFF + 854), _x_2) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_args)
    Term _k_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(1));
    e.mem[_nd_0 + 0] = _k_0;
    r0 = term_ctr(CID_IO_args, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_print)
    Term _text_0 = r0;
    Term _k_0 = r1;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = _text_0;
    e.mem[_nd_0 + 1] = _k_0;
    r0 = term_ctr(CID_IO_print, _nd_0);
    WL_RETN(1);
  }}
#endif

  WL_CASE(FID_ENTER)
    Term t = r0;
    WL_OPEN
    u32 f   = (u32)term_aux(t);
    u64 a   = term_loc(t);
    u32 war = fid_arity(f);
    WL_FRAME(t)
    seq |= fid_nofk(f) << 1;
    u32 rw = fid_resw(f);
    if (rw) {
      WL_LOAD(a + war - rw, rw)
      WL_ARGS(a, war - rw)
    } else {
      WL_LOAD(a, war)
    }
    heap_free(e, cls_fit(war + 2), a);
    WL_DYN(f);
  }}

  WL_CASE(FID_IO_emit)
    Term x = r0;
    WL_OPEN
    u64 l = heap_alloc(e, 0);
    e.mem[l] = x;
    r0 = term_ctr(CID_Emit, l);
    WL_RETN(1);
  }}

  WL_CASE(FID_Clo_apply)
    Term fun = r0;
    Term arg = r1;
    WL_OPEN
    u32 f    = (u32)term_aux(fun);
    u32 war  = fid_arity(f) - 1;
    u64 a    = term_loc(fun);
    WL_LOAD(a, war)
    spare_free(e, cls_fit(war), a);
    WL_LAST(arg)
    WL_DYN(f);
  }}

  WL_CASE(FID_EXIT)
    u32  n = rn;
    Term rv[WL_RESW];
    WL_SAVE(rv)
    WL_OPEN
    if (err_seen(e.mem)) {
      return 0;
    }
    WL_POPN(2);
    Term cont = STK(0);
    u32  idx  = (u32)STK(1);
    u32  wf   = (u32)term_aux(cont);
    if (DEVICE && wf == FID_EXIT) {
      WL_ARGS(term_loc(cont), idx)
      heap_free(e, cls_fit(STAK_LEN), term_loc(cont));
      WL_TAKE(rv)
      WL_RETN(n);
    }
    if (cont != TERM_HOLE && fid_resw(wf)) {
      u64 wa = term_loc(cont);
      u32 wn = fid_arity(wf);
      WL_FRAME(cont)
      seq = (seq & 1) | fid_nofk(wf) << 1;
      WL_ARGS(wa, wn - n)
      heap_free(e, cls_fit(wn + 2), wa);
      WL_TAKE(rv)
      WL_DYN(wf);
    }
    return task_deliver(e.mem, cont, idx, rv, n);
  }}

#if DEVICE
  default: {
    err_post(e.mem, ERR_FIDS);
    return 0;
  }
  }
  }
}
#endif

// Monk
// ====

// One turn on a ring: its head task below put0 runs (a growing lane skips a
// fork-free one, unless on the host a forking frame follows it).
INLINE u32 monk_step(Env e, DEV Term* stk, u32 rg, u32 put0, u32 base, u32 stride,
  TG u32* cur) {
  DEV u64* H   = e.mem;
  bool     seq = stride == 0;
  DEV u32* get = ring_get(H, rg);
  if (*get == put0) {
    return 0;
  }
  DEV u32* lo = (DEV u32*)ring_slot(H, rg, *get);
  u32      hi = a32_load_acq(lo + 1);
  Term     t  = (((u64)hi << 32) | a32_load(lo)) & ~RFC_BIT;
  if ((hi >> 31) != ring_lap(*get) || (!seq && fid_nofk((u32)term_aux(t)))) {
    return 0;
  }
  a32_store(get, *get + 1);
  u32 spin = 0;
  for (;;) {
    Term r = work_loop(e, stk, t, seq);
    if (r == 0) {
      return 2;
    }
    if ((u32)H[task_tail(r) + 1] == 0) {
      bool nofk = fid_nofk((u32)term_aux(r));
      Term k    = H[task_tail(r)];
      if (err_spun(H, &spin)) {
        return 2;
      }
      if (stride != 0 && nofk && (DEVICE || k == TERM_HOLE
        || !fid_resw((u32)term_aux(k)) || fid_nofk((u32)term_aux(k)))) {
        ring_push(H, ring_pick(base, stride, cur), r);
        return 2;
      }
      t      = r;
      seq    = false;
      stride = nofk ? stride : 0;
      continue;
    }
    task_deal(H, r, base, stride, cur);
    return 1;
  }
}

// Dev
// ===

// One kernel: pass 0 grows the frontier until its group is full or nothing
// grew, pass 1 runs the c-th deal on lane c, pass 3 is pass 1 on the lane's
// own ring after a small grow, and pass 2 slides each bank's [top, wr) onto
// rd in one group. TG_HOLD words of threadgroup memory keep one group per
// Apple core.

#if DEVICE

INLINE void dev_cut(Env e) {
  if (err_seen(e.mem)) {
    return;
  }
  for (u32 c = 0; c < NCLS_ALL; c += 1) {
    u64 gen = (u64)KEEP(c) << c;
    while (ALC_LEN(e, c) >= gen) {
      u64 head = ALC_AT(e, c);
      u64 tail = head;
      for (u32 i = 1; i < KEEP(c); i += 1) {
        tail = e.mem[tail];
      }
      ALC_AT(e, c)    = e.mem[tail];
      ALC_LEN(e, c)  -= gen;
      e.mem[tail]     = 0;
      bank_push(e.mem, c, head);
    }
  }
}

INLINE void bank_pack(DEV u64* H, u32 lane) {
  for (u32 c = 0; c < NCLS_ALL; c += 1) {
    DEV Bank* b  = bank_at(H, c);
    u32       rd = b->rd;
    u32       n  = b->wr - b->top;
    for (u32 i = 0; i < n; i += CUBE_T) {
      Term v = i + lane < n ? H[b->off + b->top + i + lane] : 0;
      BAR();
      if (i + lane < n) {
        H[b->off + rd + i + lane] = v;
      }
    }
    BAR();
    if (lane == 0) {
      b->rd = b->wr = b->top = rd + n;
    }
  }
}

#ifdef __METAL_VERSION__
kernel void bend_dev(DEV u64* H [[buffer(0)]], constant u32& pass [[buffer(1)]],
  TG u32* vote [[threadgroup(0)]],
  u32 grids [[threadgroups_per_grid]],
  u32 row [[threadgroup_position_in_grid]],
  u32 lane [[thread_position_in_threadgroup]]) {
#else
extern "C" __global__ void bend_dev(DEV u64* H, u32 pass, u32 at) {
  __shared__ u32 vote[3];
  u32 grids = gridDim.x;
  u32 row   = blockIdx.x;
  u32 lane  = threadIdx.x;
  if (!turn_groups(H[H_FRONT], at)) {
    return;
  }
#endif
  if (pass == 2) {
    bank_pack(H, lane);
    if (lane == 0) {
      turn_set(H, root_done(H) || err_seen(H) ? 0
        : a32_exch(a32_at(H, H_CURSOR), 0));
    }
    return;
  }
  u32 stride = grids == 1 ? CUBE_G : 1;
  u32 me     = row * CUBE_T + stride * lane;
  u32 rg     = pass == 1 ? ring_flip(me) : me;
  Env e      = { H, H + ALC_OFF + me };
  DEV Term* stk = (DEV Term*)(H + STAK_OFF + me);
  if (lane == 0) {
    for (u32 i = 0; i < 3; i += 1) {
      a32_store(vote + i, 0);
    }
  }
  BAR();
  u32 put0      = a32_load(pass == 3 ? ring_held(H, rg) : ring_put(H, rg));
  u32 seen_has  = 0;
  u32 seen_grew = 0;
  for (;;) {
    if (pass) {
      if (*ring_get(H, rg) == put0 || err_seen(H)) {
        break;
      }
    } else {
      put0 = a32_load(ring_put(H, rg));
      u32 has = put0 != a32_load(ring_get(H, rg));
      if (lane == 0 && (err_seen(H) || root_done(H))) {
        has = CUBE_T;
      }
      a32_add(vote + 2, has);
      BAR();
      has = a32_load(vote + 2);
      if (has - seen_has >= CUBE_T) {
        break;
      }
      seen_has = has;
    }
    u32 ran = monk_step(e, stk, rg, put0, row * CUBE_T, pass ? 0 : stride,
      vote);
    if (!pass) {
      if (ran == 1) {
        a32_add(vote + 1, 1);
      }
      BARD();
      u32 grew = a32_load(vote + 1);
      if (grew == seen_grew) {
        break;
      }
      seen_grew = grew;
    }
  }
  if (pass == 0) {
    a32_store(ring_held(H, rg), a32_load(ring_put(H, rg)));
  }
  dev_cut(e);
}

#endif

// Window
// ======

// Linux's window fill (the Mac's is window_msl): an Image is a quadtree over
// 2^k x 2^k (Qua splits tl, tr, bl, br; Pix is 0xRRGGBB).
#if __linux__ || BEND_RTC

INLINE u32 window_pix(DEV u64* H, Term t, u32 k, u32 x, u32 y) {
  for (u32 i = k; term_tag(t) == TAG_CTR;) {
    u32 j = 0;
    if (i > 0) {
      i -= 1;
      j = ((y >> i) & 1) * 2 + ((x >> i) & 1);
    }
    t = H[term_peek(H, t) + j];
  }
  return (u32)term_loc(t) & 0xFFFFFF;
}

#ifdef BEND_RTC
extern "C" __global__ void window_dev(DEV u64* H, Term root, u32 w, u32 h,
  u32 k, u32* out) {
  u32 x = blockIdx.x * blockDim.x + threadIdx.x;
  u32 y = blockIdx.y * blockDim.y + threadIdx.y;
  if (x < w && y < h) {
    out[y * w + x] = window_pix(H, root, k, x, y);
  }
}
#endif

#endif

#if !DEVICE

// Row
// ===

static u64 io_tick(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000000000ull + ts.tv_nsec;
}

// A row runs what precedes its forks on one thread; with fewer rows than
// threads, a grow past 1 ms deals its forks over the rows for idle threads.
static u32 row_grow(Env e, DEV Term* stk, u32 base, u32 stride, u32 want,
  u32 rows) {
  u64* H = e.mem;
  u32 cur = 0;
  u64 end = rows < pool_size ? io_tick() + 1000000 : ~0ull;
  for (;;) {
    u32 put0[CUBE_T];
    u32 has = 0;
    for (u32 i = 0; i < CUBE_T; i += 1) {
      put0[i] = *ring_put(H, base + i * stride);
      has += put0[i] != *ring_get(H, base + i * stride);
    }
    if (root_done(H) || has >= want) {
      return cur;
    }
    bool slow = io_tick() > end;
    u32 grew = 0;
    u32 ran  = 0;
    for (u32 i = 0; i < CUBE_T && ran != 2; i += 1) {
      ran   = monk_step(e, stk, base + i * stride, put0[i], slow ? 0 : base,
        slow ? CUBE_G : stride, slow ? a32_at(H, H_CURSOR) : &cur);
      grew += ran == 1;
    }
    if (grew == 0 || slow) {
      return cur;
    }
  }
}

// Pool
// ====

static void* pool_try(void* at, u64 bytes) {
  return mmap(at, bytes, PROT_READ | PROT_WRITE,
    MAP_PRIVATE | MAP_ANON | MAP_NORESERVE, -1, 0);
}

static void* pool_mmap(u64 bytes) {
  void* p = pool_try(NULL, bytes);
  if (p == MAP_FAILED) {
    err_fail("reservation failed");
  }
  return p;
}

static Term* pool_stack(void) {
  u64   len = 1ull << 31;
  u64   alt = 4 * SIGSTKSZ;
  char* p   = pool_mmap(len + 16384 + alt);
  if (mprotect(p + len, 16384, PROT_NONE)) {
    err_fail("stack guard failed");
  }
  stack_t ss = { .ss_sp = p + len + 16384, .ss_size = alt };
  sigaltstack(&ss, NULL);
  struct sigaction sa = { .sa_handler = err_trap,
    .sa_flags = SA_ONSTACK | SA_NODEFER };
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
  return (Term*)p;
}

// A wait yields a while before it sleeps, so a short turn pays no wake.

#define POOL_WAIT(c, cv) \
  for (u32 s = 0; s < 128 && (c); s += 1) { \
    sched_yield(); \
  } \
  pthread_mutex_lock(&pool_lock); \
  while (c) { \
    pthread_cond_wait(&cv, &pool_lock); \
  } \
  pthread_mutex_unlock(&pool_lock);

static u32 pool_step(u32 rows) {
  u32 per = rows * CUBE_T / (32 * pool_size);
  return CUBE_T >> (31 - CLZ(per < LINE ? per | 1 : LINE));
}

static u32 pool_rows(Env e, DEV Term* stk) {
  u32 n = 0;
  for (;;) {
    u32 c    = a32_add(&pool_row, 1);
    u32 r    = c & 32767;
    u32 rows = c >> 15 & 255;
    u32 step = c >> 23 & 1 ? 1 : pool_step(rows);
    if (r >= rows * step) {
      if (n != 0 && a32_sub_rel(&pool_done, n) == n) {
        pthread_mutex_lock(&pool_lock);
        pthread_cond_signal(&pool_join);
        pthread_mutex_unlock(&pool_lock);
      }
      return c >> 24;
    }
    a32_acq(&pool_row);
    if (c >> 23 & 1) {
      row_grow(e, stk, r * CUBE_T, 1, CUBE_T, rows);
    } else {
      u32 row = r / step * CUBE_T;
      for (u32 rg = row + r % step; rg < row + CUBE_T; rg += step) {
        u32 put0 = a32_load(ring_put(e.mem, rg));
        while (*ring_get(e.mem, rg) != put0) {
          monk_step(e, stk, rg, put0, rg, 0, NULL);
        }
      }
    }
    n += 1;
  }
}

static void* pool_work(void* arg) {
  Term* stk  = pool_stack();
  u32   seen = 0;
  for (;;) {
    POOL_WAIT(a32_load(&pool_row) >> 24 == seen, pool_wake)
    seen = pool_rows((Env){ CORPUS, ALC[(uintptr_t)arg] }, stk);
  }
}

OUTLINE void pool_open(void) {
  static bool up;
  if (up) {
    return;
  }
  up = true;
  for (u32 w = 1; w < pool_size; w += 1) {
    pthread_t tid;
    if (pthread_create(&tid, NULL, pool_work, (void*)(uintptr_t)w)) {
      err_fail("pthread_create");
    }
  }
}

static int cpu_read(const char* path, long* a, long* b) {
  FILE* f = fopen(path, "r");
  if (f == NULL) {
    return 0;
  }
  int n = fscanf(f, "%ld %ld", a, b);
  fclose(f);
  return n;
}

static long cpu_count(void) {
  long n = sysconf(_SC_NPROCESSORS_ONLN);
#ifdef __linux__
  cpu_set_t set;
  if (sched_getaffinity(0, sizeof set, &set) == 0) {
    n = CPU_COUNT(&set);
  }
  long q = 0;
  long p = 0;
  if (cpu_read("/sys/fs/cgroup/cpu.max", &q, &p) != 2) {
    cpu_read("/sys/fs/cgroup/cpu/cpu.cfs_quota_us", &q, &p);
    cpu_read("/sys/fs/cgroup/cpu/cpu.cfs_period_us", &p, &p);
  }
  if (q > 0 && p > 0 && (q + p - 1) / p < n) {
    n = (q + p - 1) / p;
  }
#endif
  return n;
}

OUTLINE void pool_turn(bool grow, u32 rows) {
  static u32 turn;
  u32 n = rows < CUBE_G ? rows : CUBE_G;
  turn += 1;
  a32_store(&pool_done, grow ? n : n * pool_step(n));
  pthread_mutex_lock(&pool_lock);
  a32_store_rel(&pool_row, turn << 24 | grow << 23 | n << 15);
  pthread_cond_broadcast(&pool_wake);
  pthread_mutex_unlock(&pool_lock);
  pool_rows((Env){ CORPUS, ALC[0] }, io_stk);
  POOL_WAIT(a32_load_acq(&pool_done) != 0, pool_join)
}

// Gpu
// ===

// gpu_make compiles the device program into <binary>.gpu: Metal's binary
// archive, or CUDA's cubin behind a hash of the text; a launch loads it or
// compiles. CUDA sizes the bag by L2 (a group per 64 KB, 16..128) and runs
// one stream, which starts faster.

static const char* gpu_path(void) {
  static char path[4096];
  u32 n = sizeof path - 8;
#ifdef __APPLE__
  _NSGetExecutablePath(path, &n);
#else
  path[readlink("/proc/self/exe", path, n)] = 0;
#endif
  return strcat(path, ".gpu");
}

static void gpu_note(const char* path) {
  fprintf(stderr, "bend: compiling the GPU program (%s is missing or"
    " stale)\n", path);
}

#if !BEND_CUDA
#define gpu_map pool_mmap
#endif

#if BEND_METAL || BEND_CUDA

static void gpu_kernel(u32 pass, u32 at);

// Dispatch at runs on TURN_ROWS(at) groups.
static void gpu_run(void) {
  for (u32 i = 0; i < 5; i += 1) {
    gpu_kernel((u32[]){ 0, 0, 1, 3, 2 }[i], i);
  }
}

#endif

#if BEND_METAL

static void gpu_fail(NSError* err) {
  err_fail([[err localizedDescription] UTF8String]);
}

static const char* gpu_probe(void) {
  gpu_dev = MTLCreateSystemDefaultDevice();
  return gpu_dev == nil ? "this binary found no usable Metal GPU" : NULL;
}

static MTLComputePipelineDescriptor* gpu_desc(void) {
  NSError* err = nil;
  MTLCompileOptions* opts = [MTLCompileOptions new];
  opts.mathMode = MTLMathModeSafe;
  opts.preprocessorMacros = @{ @"CUBE_LOG": @(CUBE_LOG) };
  id<MTLLibrary> lib = [gpu_dev newLibraryWithSource:@(BEND_SRC) options:opts
    error:&err];
  if (!lib) {
    gpu_fail(err);
  }
  MTLComputePipelineDescriptor* d = [MTLComputePipelineDescriptor new];
  d.computeFunction = [lib newFunctionWithName:@"bend_dev"];
  return d;
}

static bool gpu_make(const char* path) {
  NSError* err = nil;
  id<MTLBinaryArchive> ar = [gpu_dev
    newBinaryArchiveWithDescriptor:[MTLBinaryArchiveDescriptor new] error:&err];
  if (![ar addComputePipelineFunctionsWithDescriptor:gpu_desc() error:&err]) {
    gpu_fail(err);
  }
  return [ar serializeToURL:[NSURL fileURLWithPath:@(path)] error:&err];
}

static id<MTLComputePipelineState> gpu_pipe(MTLComputePipelineDescriptor* d,
  id<MTLBinaryArchive> ar) {
  NSError* err = nil;
  d.binaryArchives = ar ? @[ar] : @[];
  id<MTLComputePipelineState> pso = [gpu_dev
    newComputePipelineStateWithDescriptor:d
    options:ar ? MTLPipelineOptionFailOnBinaryArchiveMiss : 0 reflection:nil
    error:&err];
  if (!pso && !ar) {
    gpu_fail(err);
  }
  return pso;
}

static u64 gpu_span(void) {
  u64 span = [gpu_dev recommendedMaxWorkingSetSize];
  u64 most = [gpu_dev maxBufferLength];
  span = span < most ? span : most;
  return span < (2ull << 30) ? span : 2ull << 30;
}

static void gpu_load(u64 bytes) {
  gpu_buf = [gpu_dev newBufferWithBytesNoCopy:CORPUS length:bytes
    options:MTLResourceStorageModeShared
      | MTLResourceHazardTrackingModeUntracked deallocator:nil];
  if (!gpu_buf) {
    u64  most = [gpu_dev maxBufferLength];
    char msg[96];
    snprintf(msg, sizeof msg, "--gpu %lluMB is over the device's %lluMB",
      (unsigned long long)(bytes >> 20), (unsigned long long)(most >> 20));
    err_fail(bytes > most ? msg : "the GPU span is more than the device has");
  }
  @autoreleasepool {
    gpu_que = [gpu_dev newCommandQueue];
    const char* path = gpu_path();
    MTLBinaryArchiveDescriptor* ad = [MTLBinaryArchiveDescriptor new];
    ad.url = [NSURL fileURLWithPath:@(path)];
    MTLComputePipelineDescriptor* d = gpu_desc();
    id<MTLBinaryArchive> ar = [gpu_dev newBinaryArchiveWithDescriptor:ad
      error:nil];
    gpu_pso = ar ? gpu_pipe(d, ar) : nil;
    if (!gpu_pso) {
      gpu_note(path);
      gpu_pso = gpu_pipe(d, nil);
    }
  }
}

static void gpu_kernel(u32 pass, u32 at) {
  [gpu_enc setBytes:&pass length:sizeof pass atIndex:1];
  [gpu_enc dispatchThreadgroupsWithIndirectBuffer:gpu_buf
    indirectBufferOffset:H_GROUPS * 8 + at * 12
    threadsPerThreadgroup:MTLSizeMake(CUBE_T, 1, 1)];
  [gpu_enc memoryBarrierWithScope:MTLBarrierScopeBuffers];
}

// A bang queues each round in its own command buffer, GPU_DEEP in flight,
// chained by one event, until the pack empties the frontier (a round queued
// past that dispatches no groups).

#define GPU_DEEP 3

static id<MTLEvent> gpu_ev;
static u64          gpu_ev_at;

static void gpu_pass(u64* H) {
  id<MTLCommandBuffer> cb[GPU_DEEP] = { nil };
  gpu_ev = gpu_ev ? gpu_ev : [gpu_dev newEvent];
  for (u32 i = 0, left = GPU_DEEP; left != 0; i += 1) {
    @autoreleasepool {
      id<MTLCommandBuffer> c = cb[i % GPU_DEEP];
      [c waitUntilCompleted];
      if ([c error]) {
        gpu_fail([c error]);
      }
      left -= left < GPU_DEEP || ((volatile u64*)H)[H_FRONT] == 0;
      cb[i % GPU_DEEP] = c = left == GPU_DEEP ? [gpu_que commandBuffer] : nil;
      if (c) {
        [c encodeWaitForEvent:gpu_ev value:gpu_ev_at];
        gpu_enc = [c computeCommandEncoder];
        [gpu_enc setComputePipelineState:gpu_pso];
        [gpu_enc setBuffer:gpu_buf offset:0 atIndex:0];
        [gpu_enc setThreadgroupMemoryLength:TG_HOLD * 8 atIndex:0];
        gpu_run();
        [gpu_enc endEncoding];
        [c encodeSignalEvent:gpu_ev value:++gpu_ev_at];
        [c commit];
      }
    }
  }
}

#elif BEND_CUDA

static u64 gpu_hash(void) {
  u64 key = 14695981039346656037ull ^ CUBE_LOG;
  for (const char* p = BEND_SRC; *p != 0; p += 1) {
    key = (key ^ (u8)*p) * 1099511628211ull;
  }
  return key;
}

#define GPU_CHECK(fn, ...) do { \
  if ((result = fn(__VA_ARGS__)) != CUDA_SUCCESS) { why = #fn; goto fail; } \
} while (0)

static const char* gpu_probe(void) {
  static char error[192];
  const char* why;
  CUresult result;
  int managed = 0;
  CUcontext ctx;
  setenv("CUDA_DEVICE_MAX_CONNECTIONS", "1", 0);
  GPU_CHECK(cuInit, 0);
  GPU_CHECK(cuDeviceGet, &gpu_dev, 0);
  GPU_CHECK(cuDeviceGetAttribute, &managed,
    CU_DEVICE_ATTRIBUTE_CONCURRENT_MANAGED_ACCESS, gpu_dev);
  if (managed == 0) {
    return "CUDA device lacks concurrent managed access (WSL2 lacks it)";
  }
  int l2 = 1 << 23;
  cuDeviceGetAttribute(&l2, CU_DEVICE_ATTRIBUTE_L2_CACHE_SIZE, gpu_dev);
  int units = l2 >> 16;
  CUBE_LOG  = 31 - CLZ(units < 16 ? 16 : units > 128 ? 128 : units);
  GPU_CHECK(cuDevicePrimaryCtxRetain, &ctx, gpu_dev);
  result = cuCtxSetCurrent(ctx);
  if (result != CUDA_SUCCESS) {
    cuDevicePrimaryCtxRelease(gpu_dev);
    why = "cuCtxSetCurrent";
    goto fail;
  }
  return NULL;
fail:;
  const char* name = NULL;
  if (cuGetErrorName(result, &name) != CUDA_SUCCESS || name == NULL) {
    name = "unknown CUDA error";
  }
  snprintf(error, sizeof error, "%s failed: %s", why, name);
  return error;
}

#undef GPU_CHECK

static u64* gpu_map(u64 bytes) {
  CUdeviceptr p = 0;
  if (cuMemAllocManaged(&p, bytes, CU_MEM_ATTACH_GLOBAL) != CUDA_SUCCESS) {
    err_fail("corpus reservation failed");
  }
#if CUDA_VERSION >= 13000
  cuMemAdvise(p, bytes, CU_MEM_ADVISE_SET_PREFERRED_LOCATION,
    (CUmemLocation){ CU_MEM_LOCATION_TYPE_DEVICE, gpu_dev });
#else
  cuMemAdvise(p, bytes, CU_MEM_ADVISE_SET_PREFERRED_LOCATION, gpu_dev);
#endif
  return (u64*)(uintptr_t)p;
}

static bool gpu_make(const char* path) {
  int cc[2] = {0, 0};
  cuDeviceGetAttribute(cc,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, gpu_dev);
  cuDeviceGetAttribute(cc + 1,
    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, gpu_dev);
  char arch[40];
  char bag[24];
  snprintf(arch, sizeof arch, "--gpu-architecture=sm_%d%d", cc[0], cc[1]);
  snprintf(bag, sizeof bag, "-DCUBE_LOG=%u", CUBE_LOG);
  const char* opts[] = { arch, bag, "--fmad=false", "-default-device" };
  nvrtcProgram prog;
  if (nvrtcCreateProgram(&prog, BEND_SRC, "bend.cu", 0, NULL, NULL)
    != NVRTC_SUCCESS) {
    err_fail("cannot compile the CUDA library");
  }
  if (nvrtcCompileProgram(prog, 4, opts) != NVRTC_SUCCESS) {
    size_t n = 0;
    nvrtcGetProgramLogSize(prog, &n);
    char* log = calloc(n + 1, 1);
    if (log != NULL && nvrtcGetProgramLog(prog, log) == NVRTC_SUCCESS) {
      fprintf(stderr, "%s\n", log);
    }
    err_fail("cannot compile the CUDA library");
  }
  size_t len = 0;
  nvrtcGetCUBINSize(prog, &len);
  char* bin = malloc(len);
  if (bin == NULL || nvrtcGetCUBIN(prog, bin) != NVRTC_SUCCESS) {
    err_fail("cannot load the CUDA library");
  }
  nvrtcDestroyProgram(&prog);
  u64   key = gpu_hash();
  FILE* out = fopen(path, "wb");
  bool  ok  = out != NULL && fwrite(&key, 8, 1, out) == 1
    && fwrite(bin, 1, len, out) == len && fclose(out) == 0;
  if (cuModuleLoadData(&gpu_lib, bin) != CUDA_SUCCESS) {
    err_fail("cannot load the CUDA library");
  }
  free(bin);
  return ok;
}

static u64 gpu_span(void) {
  size_t span = 0;
  cuDeviceTotalMem(&span, gpu_dev);
  return span;
}

static void gpu_load(u64 bytes) {
  const char* path = gpu_path();
  int         fd   = open(path, O_RDONLY);
  struct stat st   = { 0 };
  u64         key  = 0;
  char*       bin  = fd < 0 || fstat(fd, &st) != 0 || st.st_size <= 8 ? NULL
    : mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (bin != NULL && bin != MAP_FAILED) {
    memcpy(&key, bin, 8);
  }
  if (key != gpu_hash()
    || cuModuleLoadData(&gpu_lib, bin + 8) != CUDA_SUCCESS) {
    gpu_note(path);
    gpu_make(path);
  }
  if (cuModuleGetFunction(&gpu_pso, gpu_lib, "bend_dev") != CUDA_SUCCESS) {
    err_fail("cannot load the GPU program");
  }
}

static void gpu_kernel(u32 pass, u32 at) {
  void* args[] = { &CORPUS, &pass, &at };
  if (cuLaunchKernel(gpu_pso, TURN_ROWS(at), 1, 1, CUBE_T, 1, 1, 0, NULL,
    args, NULL) != CUDA_SUCCESS) {
    err_fail("device launch failed");
  }
}

// A bang launches 1, 2, 4 .. 64 rounds between syncs, until the pack
// empties the frontier. A pass launched past that returns at once.
static void gpu_pass(u64* H) {
  for (u32 n = 1; H[H_FRONT] != 0; n = n < 32 ? 2 * n : 64) {
    for (u32 i = 0; i < n; i += 1) {
      gpu_run();
    }
    if (cuCtxSynchronize() != CUDA_SUCCESS) {
      err_fail("device fault");
    }
  }
}

#else

#define gpu_probe() "this binary has no CUDA or Metal GPU support"
#define gpu_make(p) true
#define gpu_span()  0
#define gpu_load(b)
#define gpu_pass(H)

#endif

// Cube
// ====

// The host's column grows only to a LINE of tasks a thread, as every task a
// grow starts is live at once; pool_step splits the few rows instead. A turn
// visits only the rows below its bound, which hold every task: a drain deals
// task g to ring_flip(g), at row g at most, and a grow's cur tasks land in
// rows 0 to cur - 1. A slow grow deals task g to row g % CUBE_T.

static void ring_rewind(u64* H, u32 rows) {
  Term keep[RING_LEN];
  for (u32 r = 0; r < (rows < CUBE_G ? rows : CUBE_G) * CUBE_T; r += 1) {
    u32 g = *ring_get(H, r);
    u32 n = *ring_put(H, r) - g;
    if (g == 0) {
      continue;
    }
    for (u32 i = 0; i < n; i += 1) {
      keep[i] = *ring_slot(H, r, g + i) & ~RFC_BIT;
    }
    for (u32 i = n; i < g + n && i < RING_LEN; i += 1) {
      ((u32*)ring_slot(H, r, i))[1] = 0;
    }
    *ring_get(H, r) = *ring_put(H, r) = 0;
    for (u32 i = 0; i < n; i += 1) {
      ring_push(H, r, keep[i]);
    }
  }
}

static void cube_run(u64* H, bool gpu) {
  u32 f = a32_exch(a32_at(H, H_CURSOR), 0);
  if (gpu) {
    turn_set(H, f);
  }
  while (!root_done(H)) {
    if (f == 0) {
      err_fail("frontier drained without a result");
    }
    if (gpu) {
      gpu_pass(H);
      f = (u32)H[H_FRONT];
    } else {
      u32 rows = f;
      u32 want = (pool_size - 1) / (CUBE_T / LINE) + 1;
      if (f < want) {
        u32 cur = row_grow((Env){ H, ALC[0] }, io_stk, 0, CUBE_G, want, f);
        rows = cur > f ? cur : f;
      }
      for (u32 g = f; g != 0 && f < CUBE;
        g = a32_exch(a32_at(H, H_CURSOR), 0)) {
        rows = g > rows ? g : rows;
        pool_turn(true, rows);
      }
      pool_turn(false, rows);
      f = a32_exch(a32_at(H, H_CURSOR), 0);
      ring_rewind(H, f > rows ? f : rows);
    }
    u32 ec = a32_load(a32_at(H, H_ERROR_CODE));
    if (ec != 0) {
      err_post(H, ec);
    }
  }
  a32_store(a32_at(H, H_CURSOR), 0);
}

// Corpus
// ======

// The cores map 8 GiB at a high base and double it in place; the banks move
// up past the pages. The GPU maps its whole span once.

static u64 corpus_size;

static bool corpus_at(void* at, u64 size) {
  void* p = pool_try(at, size);
  if (p != MAP_FAILED && p != at) {
    munmap(p, size);
  }
  return p == at;
}

static void* corpus_map(u64 size) {
  for (u64 hint = 1ull << 45; hint > size; hint /= 2) {
    if (corpus_at((void*)hint, size)) {
      return (void*)hint;
    }
  }
  return pool_mmap(size);
}

static void corpus_lay(u64* H, u64 size) {
  u64 span = size / 8;
  u64 cap  = span > HEAP_OFF ? (span - HEAP_OFF) / (PAGE_LEN + 10) : 0;
  if (cap <= CUBE) {
    err_fail("the GPU span is under the rings, stacks and a page per lane");
  }
  cap = cap < ~0u ? cap : ~0u - 1;
  u64 at = HEAP_OFF + (cap << PAGE_BITS);
  for (u32 c = 0; c < NCLS_ALL; c += 1) {
    Bank* b = bank_at(H, c);
    memcpy(H + at, H + b->off, b->wr * sizeof(u64));
    b->off  = at;
    at     += 2 * (cap >> ((c < NCLS ? NCLS : c) - PAGE_BITS));
  }
  corpus_size = size;
  a32_store_rel(a32_at(H, H_CAP), (u32)cap);
}

static bool corpus_grow(u64* H, u64 need) {
  bool ok = true;
  LOCK(bank_lock);
  while (ok && need > a32_load(a32_at(H, H_CAP))) {
    u64 more = corpus_size;
    ok = !io_gpu && more < 1ull << 43 && corpus_at((char*)H + more, more);
    if (ok) {
      corpus_lay(H, more * 2);
    }
  }
  UNLOCK(bank_lock);
  return ok;
}

static u64* corpus_setup(bool gpu, long threads, u64 bytes) {
  io_gpu     = gpu;
  KEEP_WORDS = gpu ? CHUNK : CAP_WORDS;
  u64 size   = (!gpu ? 1ull << 33 : bytes != 0 ? bytes : gpu_span())
    & ~16383ull;
  CORPUS     = gpu ? gpu_map(size) : corpus_map(size);
  u64* H     = CORPUS;
#if BEND_CUDA
  if (gpu) {
    cuMemsetD8((CUdeviceptr)(uintptr_t)H, 0, STAK_OFF * 8);
    cuCtxSynchronize();
  }
#endif
  corpus_lay(H, size);
  memcpy(H + STAT_OFF, STAT_IMG, STAT_LEN * sizeof(u64));
  a32_store(a32_at(H, H_BUMP), 1);
  if (gpu) {
    gpu_load(size);
  }
  pool_size = threads < 1 ? 1 : threads < CUBE_T ? threads : CUBE_T;
  return H;
}

OUTLINE Term corpus_eval(u64* H, Term t) {
  Env  e = { H, ALC[0] };
  Term rv[WL_RESW];
  while ((t = work_loop(e, io_stk, t, !BANGS && pool_size == 1)) != 0) {
    u64 tl = task_tail(t);
    if ((u32)H[tl + 1] != 0) {
      task_deal(H, t, 0, 0, NULL);
      pool_open();
      cube_run(H, false);
      break;
    }
    if (io_gpu && fid_bangs((u32)term_aux(t))) {
      Term cont = H[tl];
      u32  idx  = (u32)(H[tl + 1] >> 32) & 0xFFFF;
      H[tl]     = TERM_HOLE;
      a32_store(a32_at(H, H_CURSOR), 1);
      ring_push(H, 0, t);
      cube_run(H, true);
      t = task_deliver(H, cont, idx, rv, root_take(H, rv));
      if (t == 0) {
        break;
      }
    }
  }
  if (!root_done(H)) {
    err_fail("a delivery lost");
  }
  root_take(H, rv);
  return rv[0];
}

// Io
// ==

// Base's opaque, linear handles pack host fds or pointers into aux and loc.
// A request's cont applied to its item is the next request. A parked
// request keeps its fd, deadline and events in word, time and evts; once
// due, pack resumes it or parks it again (IO_PARK). Text is UTF-8, decoded
// as WHATWG does. io_sys_addr refuses a leading zero (octal to some libcs).
// macOS poll misses FIFO EOF, so io_wait selects, sized to the highest fd.

#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <sys/socket.h>

#define IO_PARK TERM_HOLE

#define io_hand(v)   term_make(TAG_PAK, (u64)(v) >> 40, (u64)(v) & LOC_MASK)
#define io_hand_v(t) ((term_aux(t) << 40) | term_loc(t))

typedef struct IoWork IoWork;
typedef void (*IoCall)(IoWork* w);
typedef Term (*IoPack)(Env e, IoWork* w);

struct IoWork {
  intptr_t hand;
  intptr_t made;
  u32      word;
  u64      size;
  char*    data;
  char*    text;
  u32      code;
  IoCall   call;
  IoPack   pack;
  Term     cont;
  Term     item;
  u64      time;
  short    evts;
  IoWork*  next;
  IoWork*  prev;
};

typedef Term (*Effect)(Env e, Term* f, IoWork* w);

Effect io_eff_rows[sizeof CID_T / sizeof *CID_T];
static u32    io_live;

OUTLINE void* io_mem(void* mem) {
  if (mem == NULL) {
    err_fail("host allocation failed");
  }
  return mem;
}

static int io_sys_addr(const char* host, u32 port, struct sockaddr_in* at) {
  *at = (struct sockaddr_in){ .sin_family = AF_INET,
    .sin_port = htons((uint16_t)port) };
  for (const char* p = host; *p != 0; p += 1) {
    if ((p == host || p[-1] == '.') && *p == '0'
      && p[1] >= '0' && p[1] <= '9') {
      return -1;
    }
  }
  return port > 65535 || inet_pton(AF_INET, host, &at->sin_addr) != 1
    ? -1 : 0;
}

static int    io_argc;
static char** io_argv;

static void io_eff(u32 cid, Effect run) {
  if (io_eff_rows[cid] != NULL) {
    err_fail("two effects register one request");
  }
  io_eff_rows[cid] = run;
}

static u64 io_sys_end(IoWork* w, ssize_t n) {
  w->code = n < 0 ? (u32)errno : 0;
  return n < 0 ? 0 : (u64)n;
}

static IoWork* io_runs;
static IoWork* io_park;
static IoWork* io_jobs;

static void io_push(IoWork** q, IoWork* a) {
  IoWork* l = *q != NULL ? *q : a;
  a->next = l->next;
  l->next = a;
  *q      = a;
}

static IoWork* io_pop(IoWork** q) {
  IoWork* a  = (*q)->next;
  (*q)->next = a->next;
  *q         = a != *q ? *q : NULL;
  return a;
}

static void io_spawn(Term m) {
  IoWork* a = io_mem(calloc(1, sizeof(IoWork)));
  a->cont  = m;
  a->item  = term_clo(FID_IO_emit, 0);
  io_push(&io_runs, a);
  io_live += 1;
}

// io_park stays in deadline order (time 0, none, sorts last; ties keep
// their park order).
static void io_park_add(IoWork* w) {
  IoWork* p = io_park;
  if (p == NULL || p->time - 1 <= w->time - 1) {
    io_push(&io_park, w);
  } else {
    while (p->next->time - 1 <= w->time - 1) {
      p = p->next;
    }
    io_push(&p, w);
  }
  w->prev       = w->next == w ? w : w->next->prev;
  w->next->prev = w;
}

static void io_park_cut(IoWork* w) {
  w->prev->next = w->next;
  w->next->prev = w->prev;
  io_park = w->next == w ? NULL : io_park == w ? w->prev : io_park;
}

#define io_parked(a) for (IoWork* a = io_park; a != NULL; \
  a = a->next != io_park ? a->next : NULL)

static Term io_wait_on(IoWork* w, int fd, short evts, u64 time, IoPack more) {
  w->word = (u32)fd;
  w->pack = more;
  w->time = time;
  w->evts = evts;
  io_park_add(w);
  return IO_PARK;
}

static void io_lost(void) {
  if (errno == EPIPE) {
    signal(SIGPIPE, SIG_DFL);
    raise(SIGPIPE);
  }
  err_fail("a short write on a standard stream");
}

OUTLINE void io_out(FILE* h, const char* data, u64 len) {
  if (fwrite(data, 1, len, h) != len) {
    io_lost();
  }
}

OUTLINE void io_sync(void) {
  if (fflush(stdout) != 0) {
    io_lost();
  }
}

static u64 io_utf8(char* buf, u64 c) {
  c = c > 0x10FFFF || (c >= 0xD800 && c <= 0xDFFF) ? 0xFFFD : c;
  u64 k = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
  for (u64 i = k; i > 1; i -= 1) {
    buf[i - 1] = (char)(0x80 | (c & 0x3F));
    c >>= 6;
  }
  buf[0] = (char)(k == 1 ? c : (0xF00 >> k) | c);
  return k;
}

// io_cbuf writes a String (cons SCon) as UTF-8, or a List (cons Con) as
// its bytes, with no UTF-8: NULL if a value is past 255.
OUTLINE char* io_cbuf(Env e, Term s, u64* len, u64 cons) {
  u64   cap = 64, n = 0, bad = 0;
  char* buf = io_mem(malloc(cap));
  while (term_aux(s) == cons) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n + 5 > cap) {
      cap *= 2;
      buf = io_mem(realloc(buf, cap));
    }
    if (cons == CID_SCon) {
      n += io_utf8(buf + n, fb[0]);
    } else {
      bad |= fb[0] > 255;
      buf[n++] = (char)fb[0];
    }
    s = fb[1];
  }
  buf[n] = 0;
  *len = n;
  if (bad) {
    free(buf);
    return NULL;
  }
  return buf;
}

#define io_cstr(e, s, len) io_cbuf(e, s, len, CID_SCon)

OUTLINE void io_errs(Env e, Term s) {
  u64   n;
  char* text = io_cstr(e, s, &n);
  io_sync();
  text[n] = '\n';
  io_out(stderr, text, n + 1);
  free(text);
}

#define io_nul(s, n) (strlen(s) != (n))

#define io_seal(e, t, cid) (cid_hot(cid) ? rfc_seal(e, t) : (t))

static Term io_node(Env e, u64 cid, Term a, Term b) {
  u64 l = heap_alloc(e, 1);
  e.mem[l]     = io_seal(e, a, cid);
  e.mem[l + 1] = io_seal(e, b, cid);
  return term_ctr(cid, l);
}

static Term io_str(Env e, const char* p, u64 n) {
  Term  s;
  Term* hole = &s;
  u64  c = 0, need = 0, lo = 0x80, hi = 0xBF;
  for (u64 i = 0; i < n || need > 0; i += 1) {
    u64 b = i < n ? (uint8_t)p[i] : 0x100;
    if (need > 0 && (b < lo || b > hi)) {
      need = 0;
      c    = 0xFFFD;
      i   -= 1;
    } else if (need > 0) {
      lo = 0x80;
      hi = 0xBF;
      c  = (c << 6) | (b & 0x3F);
      if (--need > 0) {
        continue;
      }
    } else if (b < 0x80) {
      c = b;
    } else if (b < 0xC2 || b > 0xF4) {
      c = 0xFFFD;
    } else {
      need = b < 0xE0 ? 1 : b < 0xF0 ? 2 : 3;
      lo   = b == 0xE0 ? 0xA0 : b == 0xF0 ? 0x90 : 0x80;
      hi   = b == 0xED ? 0x9F : b == 0xF4 ? 0x8F : 0xBF;
      c    = b & (0x3F >> need);
      continue;
    }
    u64  l = heap_alloc(e, 1);
    Term t = term_ctr(CID_SCon, l);
    e.mem[l] = c;
    *hole = hole == &s ? t : io_seal(e, t, CID_SCon);
    hole = &e.mem[l + 1];
  }
  *hole = term_pak(CID_SNil, 0);
  return s;
}

#ifdef CID_Con

static Term io_list(Env e, const char* p, u64 n) {
  Term xs = term_pak(CID_Nil, 0);
  for (u64 i = n; i > 0; i -= 1) {
    xs = io_node(e, CID_Con, (uint8_t)p[i - 1], xs);
  }
  return xs;
}

#endif

#define io_tup(e, a, b) io_node(e, CID_Tuple, a, b)
#define io_done(e, v)   io_box(e, CID_Done, v)
#define io_res(e, w, v) ((w)->code ? io_fail(e, (w)->code, NULL) \
  : io_done(e, v))
#define io_until(ms)    (io_tick() + (u64)(ms) * 1000000ull)
#define io_again(w) ((w)->code == EAGAIN \
  && ((w)->time == 0 || io_tick() < (w)->time))
#define io_poll_end(e, w, rest, r) ((w)->code == EAGAIN \
  ? io_box(e, CID_Wait, rest) : (w)->time ? io_box(e, CID_Ready, r) : (r))

static Term io_box(Env e, u64 cid, Term v) {
  u64 l = heap_alloc(e, 0);
  e.mem[l] = io_seal(e, v, cid);
  return term_ctr(cid, l);
}

static Term io_err(Env e, u32 code, const char* text) {
  const char* s = text != NULL ? text : strerror((int)code);
  return io_tup(e, code, io_str(e, s, strlen(s)));
}

#define io_fail(e, code, text) io_box(e, CID_Fail, io_err(e, code, text))

static pthread_mutex_t io_gate = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  io_bell = PTHREAD_COND_INITIALIZER;
static u32             io_busy;
static u32             io_size;
static int             io_wake_fd[2];

static void io_take(Env e) {
  IoWork* acts[64];
  ssize_t n;
  while ((n = read(io_wake_fd[0], acts, sizeof acts)) > 0) {
    for (u32 i = 0; i < (u32)n / sizeof(IoWork*); i += 1) {
      IoWork* a = acts[i];
      a->item   = a->pack(e, a);
      io_push(&io_runs, a);
      io_busy -= 1;
    }
  }
}

static void* io_help(void* arg) {
  for (;;) {
    pthread_mutex_lock(&io_gate);
    while (io_jobs == NULL) {
      pthread_cond_wait(&io_bell, &io_gate);
    }
    IoWork* a = io_pop(&io_jobs);
    pthread_mutex_unlock(&io_gate);
    a->call(a);
    while (write(io_wake_fd[1], &a, sizeof a) != sizeof a) {
    }
  }
}

static Term io_work(IoWork* w, IoCall call, IoPack pack) {
  w->call  = call;
  w->pack  = pack;
  io_busy += 1;
  if (io_busy > io_size && io_size < IO_HELP) {
    pthread_t tid;
    if (pthread_create(&tid, NULL, io_help, NULL)) {
      err_fail("pthread_create");
    }
    pthread_detach(tid);
    io_size += 1;
  }
  pthread_mutex_lock(&io_gate);
  io_push(&io_jobs, w);
  pthread_cond_signal(&io_bell);
  pthread_mutex_unlock(&io_gate);
  return IO_PARK;
}

static bool io_bit(u8* set, int fd, bool put) {
  u8* at = set + fd / 8;
  *at |= put << fd % 8;
  return *at >> fd % 8 & 1;
}

static void io_wait(Env e, bool block) {
  int top  = io_wake_fd[0];
  u64 soon = io_park != NULL ? io_park->next->time : 0;
  io_parked(a) {
    if (a->evts != 0 && (int)a->word > top) {
      top = (int)a->word;
    }
  }
  u64 len = (u64)top / 64 * 8 + 8;
  u8* set = io_mem(calloc(2, len));
  io_bit(set, io_wake_fd[0], true);
  io_parked(a) {
    if (a->evts != 0) {
      io_bit(set + (a->evts == POLLOUT) * len, (int)a->word, true);
    }
  }
  u64 tick = io_tick();
  u64 ms = soon > tick && block ? (soon - tick) / 1000000 + 1 : 0;
  struct timeval tv = { ms / 1000, ms % 1000 * 1000 };
  io_sync();
  if (select(top + 1, (fd_set*)set, (fd_set*)(set + len), NULL,
    soon == 0 && block ? NULL : &tv) < 0) {
    if (errno != EINTR) {
      err_fail("the poller failed");
    }
    memset(set, 0, 2 * len);
  }
  if (io_bit(set, io_wake_fd[0], false)) {
    io_take(e);
  }
  u64     now  = io_tick();
  IoWork* todo = io_park;
  io_park = NULL;
  while (todo != NULL) {
    IoWork* a   = io_pop(&todo);
    bool    due = (a->evts != 0
        && io_bit(set + (a->evts == POLLOUT) * len, (int)a->word, false))
      || (a->time != 0 && a->time <= now);
    if (!due) {
      io_park_add(a);
      continue;
    }
    Term x = a->pack(e, a);
    if (x != IO_PARK) {
      a->item = x;
      io_push(&io_runs, a);
    }
  }
  free(set);
}

static int f32_text(char* buf, f32 v) {
  int n = 0;
  int p = 0;
  if (v != v) {
    return sprintf(buf, "nan");
  }
  for (; p < 9; p += 1) {
    n = snprintf(buf, 40, "%.*e", p, (double)v);
    if (strtof(buf, NULL) == v) {
      break;
    }
  }
  char* ep = strchr(buf, 'e');
  if (ep == NULL) {
    return n;
  }
  int ex = atoi(ep + 1);
  if (ex >= 21 || ex <= -7) {
    return (int)(ep - buf) + sprintf(ep, "e%+d", ex);
  }
  // The scientific form has the rounded digits d, d[i] at the place ex - i:
  // write each place from the highest down, with a point before place -1.
  int  s = *buf == '-';
  char d[9];
  d[0] = buf[s];
  memcpy(d + 1, buf + s + 2, p);
  n = s;
  for (int q = ex > 0 ? ex : 0; q >= 0 || q >= ex - p; q -= 1) {
    if (q == -1) {
      buf[n++] = '.';
    }
    buf[n++] = q <= ex && q >= ex - p ? d[ex - q] : '0';
  }
  buf[n] = 0;
  return n;
}

static Term f32_show(Env e, Term x) {
  char buf[40];
  return io_str(e, buf, f32_text(buf, f32_unbox(x)));
}

static Term f32_read(Env e, Term s) {
  u64 n;
  char* text = io_cstr(e, s, &n);
  char* end;
  f32 v = strtof(text, &end);
  Term out = n > 0 && (u64)(end - text) == n && strpbrk(text, "xX(") == NULL
    ? io_box(e, CID_Some, f32_rewrap(v)) : term_pak(CID_None, 0);
  free(text);
  return out;
}


// Show
// ====

// show_val prints a pure main's value as term_show does: d is a SHOW_DESC
// node (see show_main), w its words, chain the bracket of the list or tuple
// the value continues, or 0.

#if MAIN_PURE

static void show_chr(u64 c, char q) {
  char b[4];
  int  k = c == 10 ? 'n' : c == 9 ? 't' : c == 13 ? 'r' : c == 0 ? '0'
    : c == 92 || c == (u64)q ? (int)c : 0;
  if (k != 0) {
    printf("\\%c", k);
  } else if (c < 32 || c == 127 || (c >= 0xD800 && c <= 0xDFFF)
    || c > 0x10FFFF) {
    printf("\\u{%llx}", (unsigned long long)c);
  } else {
    fwrite(b, 1, io_utf8(b, c), stdout);
  }
}

static void show_f32(Term x) {
  char buf[40];
  f32_text(buf, f32_unbox(x));
  int  m = (int)strcspn(buf, "e");
  if (strpbrk(buf, ".ni") == NULL) {
    printf("%.*s.0%s", m, buf, buf + m);
  } else {
    fputs(buf, stdout);
  }
}

static void show_val(Env e, u32 d, const Term* w, char chain) {
  const u32* D = SHOW_DESC;
  Term one;
  char zs[4];
  u32  zn = 0;
  for (bool tail = true; tail;) switch (tail = false, D[d]) {
    case 0:
      printf("%u", (u32)w[0]);
      break;
    case 1:
      show_f32(w[0]);
      break;
    case 2:
      printf("%llun", (unsigned long long)w[0]);
      break;
    case 3:
      putchar('\'');
      show_chr(D[d + 1] != 0 ? term_loc(w[0]) : w[0], '\'');
      putchar('\'');
      break;
    case 4:
      putchar('"');
      for (Term s = w[0]; term_aux(s) == CID_SCon;) {
        u64 l = term_peek(e.mem, s);
        show_chr(e.mem[l], '"');
        s = e.mem[l + 1];
      }
      putchar('"');
      break;
    case 5:
      fputs("{==}", stdout);
      break;
    case 6:
      putchar('[');
      for (u32 i = 0, g = D[d + 2]; i < 1u << (blk_cls(w[0]) - g); i += 1) {
        Term v[1u << g];
        for (u32 j = 0; j < 1u << g; j += 1) {
          v[j] = blk_read(e.mem, term_tag(w[0]) == TAG_ARR,
            term_peek(e.mem, w[0]), (i << g) + j);
        }
        fputs(i > 0 ? ", " : "", stdout);
        show_val(e, D[d + 1], v, 0);
      }
      putchar(']');
      break;
    default: {
      Term t   = w[0];
      bool box = D[d + 1] != 0;
      u32  key = box ? (u32)term_aux(t) : D[d + 2] > 1 ? (u32)t : 0;
      u32  a   = d + 3;
      for (u32 i = 0; box ? D[a + 1] != key : i != key; i += 1) {
        a += 4 + 2 * D[a + 2];
      }
      if (box) {
        one = term_loc(t);
        w   = term_tag(t) == TAG_PAK ? &one : e.mem + term_peek(e.mem, t);
      }
      char o = "{[("[D[a + 3]];
      if (o == '{') {
        fputs(SHOW_NAMES[D[a]], stdout);
      }
      if (chain != o) {
        putchar(o);
        zs[zn++] = "}])"[D[a + 3]];
      }
      for (u32 j = 0; j < D[a + 2]; j += 1) {
        if (o == '[' ? j == 0 && chain == o : j > 0) {
          fputs(", ", stdout);
        }
        if (j == 1 && o != '{') {
          tail  = true;
          chain = o;
          d     = D[a + 5 + 2 * j];
          w    += D[a + 4 + 2 * j];
        } else {
          show_val(e, D[a + 5 + 2 * j], w + D[a + 4 + 2 * j], 0);
        }
      }
    }
  }
  while (zn > 0) {
    putchar(zs[--zn]);
  }
}

#endif

// Run
// ===

static void io_step(Env e, IoWork* a) {
  for (u32 step = 0; step < 64; step += 1) {
    u64  ap  = task_node(e, FID_Clo_apply, TERM_HOLE, 0, 0);
    e.mem[ap]     = a->cont;
    e.mem[ap + 1] = a->item;
    Term req = corpus_eval(e.mem, term_tsk(FID_Clo_apply, ap));
    u32  c   = (u32)term_aux(req);
    if (c == CID_Emit) {
      term_drop(e, req);
      free(a);
      io_live -= 1;
      return;
    }
    Term fs[256];
    u32  n = cid_arity(c);
    if (term_tag(req) == TAG_PAK) fs[0] = term_loc(req);
    else spare_free(e, cls_fit(n), ctr_take(e, req, n, fs));
    if (c == CID_Halt || c == CID_Exit) {
      if (c == CID_Halt) io_errs(e, fs[1]);
      if ((u32)fs[0] > 255) err_fail("exit code must be in 0..255");
      io_sync();
      exit((int)(u32)fs[0]);
    }
    if (io_eff_rows[c] == NULL) {
      err_fail("an alien request");
    }
    a->cont = fs[n - 1];
    Term x  = io_eff_rows[c](e, fs, a);
    if (x == IO_PARK) {
      return;
    }
    a->item = x;
  }
  io_push(&io_runs, a);
}

OUTLINE void io_loop(u64* H) {
  Env e = { H, ALC[0] };
  io_stk = pool_stack();
  signal(SIGPIPE, SIG_IGN);
  if (pipe(io_wake_fd) | fcntl(io_wake_fd[0], F_SETFL, O_NONBLOCK)) {
    err_fail("the event loop failed to open");
  }
  Term m = corpus_eval(H, term_tsk(MAIN_FID, task_node(e, MAIN_FID,
    TERM_HOLE, 0, 0)));
#if MAIN_PURE
  show_val(e, 0, H + H_ROOT_WORD, 0);
  putchar('\n');
  return;
#endif
  io_spawn(m);
  u64 look = 0;
  for (u32 n = 0;; n += 1) {
    if (io_runs == NULL) {
      if (io_live == 0) {
        return;
      }
      if (io_park == NULL && io_busy == 0) {
        io_sync();
        err_fail("deadlock: every computation waits on a channel");
      }
      io_wait(e, true);
      continue;
    }
    // A busy loop still checks due timers, and fds periodically.
    if ((n & 63) == 0) {
      if (io_busy != 0) {
        io_take(e);
      }
      if (io_park != NULL) {
        u64 now = io_tick();
        if (now >= look || io_park->next->time - 1 < now) {
          look = now + 10000000;
          io_wait(e, false);
        }
      }
    }
    io_step(e, io_pop(&io_runs));
  }
}

// Requests
// ========

// IO
// ==

Term io_args_run(Env e, Term* f, IoWork* w) {
  Term xs = term_pak(CID_Nil, 0);
  for (int i = io_argc; i > 0; i -= 1) {
    const char* a = io_argv[i - 1];
    xs = io_node(e, CID_Con, io_str(e, a, strlen(a)), xs);
  }
  return xs;
}

static void __attribute__((constructor)) io_args_use(void) {
  io_eff(CID_IO_args, io_args_run);
}
// IO
// ==

Term io_print_run(Env e, Term* f, IoWork* w) {
  uint64_t n = 0;
  char* text = io_cstr(e, f[0], &n);
  text[n] = '\n';
  io_out(stdout, text, n + 1);
  free(text);
  return term_pak(CID_Unit, 0);
}

static void __attribute__((constructor)) io_print_use(void) {
  io_eff(CID_IO_print, io_print_run);
}


// Main
// ====

int main(int argc, char** argv) {
  long   thr = cpu_count();
  int    gpu = -1;
  u64    mem = 0;
  char*  env = strdup(getenv("BENDRTS") != NULL ? getenv("BENDRTS") : "");
  char** rts = malloc((argc + strlen(env) + 1) * sizeof(char*));
  int    nr  = 0;
  bool   in  = false;
  for (char* w = strtok(env, " \t\n"); w != NULL; w = strtok(NULL, " \t\n")) {
    rts[nr++] = w;
  }
  rts[nr++] = NULL;
  io_argv = argv;
  io_argc = argc > 0;
  for (int i = 1; i < argc; i += 1) {
    char* a = argv[i];
    if (!strcmp(a, "--RTS")) {
      for (i += 1; i < argc; i += 1) {
        io_argv[io_argc++] = argv[i];
      }
    } else if (!strcmp(a, "+RTS") || !strcmp(a, "-RTS")) {
      in        = a[0] == '+';
      rts[nr++] = NULL;
    } else if (in) {
      rts[nr++] = a;
    } else {
      io_argv[io_argc++] = a;
    }
  }
  for (int i = 0; i < nr; i += 1) {
    const char* a = rts[i];
    const char* v = i + 1 < nr && rts[i + 1] != NULL ? rts[i + 1] : "";
    char*       end;
    if (a == NULL) {
      continue;
    } else if (!strcmp(a, "--help")) {
      printf(CLI_HELP, argv[0]);
      return 0;
    } else if (!strcmp(a, "--gpu-build")) {
      if (gpu_probe() == NULL && !gpu_make(gpu_path())) {
        fprintf(stderr, "bend: cannot write %s\n", gpu_path());
        return 1;
      }
      return 0;
    } else if (!strcmp(a, "--threads")) {
      thr = strtol(v, NULL, 10);
      if (thr < 1 || v[strspn(v, "0123456789")] != 0) {
        err_fail("expected a thread count of 1 or more after --threads");
      }
      i += 1;
    } else if (!strcmp(a, "--gpu")) {
      double n   = strtod(v, &end);
      u64    mul = !strcmp(end, "GB") ? 1ull << 30
        : !strcmp(end, "MB") ? 1ull << 20 : 0;
      mem = (u64)(n * (double)mul);
      if (!strcmp(v, "off")) {
        gpu = 0;
      } else if (!strcmp(v, "on")
        || (mem >= 16384 && end == v + strspn(v, "0123456789."))) {
        gpu = 1;
      } else {
        err_fail("expected on, off or a size like 4GB after --gpu");
      }
      i += 1;
    } else {
      fprintf(stderr, "bend: unknown runtime option %s\n", a);
      return 1;
    }
  }
  const char* why = gpu != 0 && BANGS != 0 ? gpu_probe() : "";
  if (gpu == 1 && BANGS != 0 && why != NULL) {
    err_fail(why);
  }
  io_loop(corpus_setup(why == NULL, thr, mem));
  io_sync();
  return 0;
}

#endif
