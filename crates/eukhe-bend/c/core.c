
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
#define CID_Unknown 20
#define CID_LT 21
#define CID_EQ 22
#define CID_GT 23
#define CID_ffi_echo_Echo 24
#define CID_ffi_echo_Refused 25
#define CID_WNil 26
#define CID_wire_Got 27
#define CID_wire_Bad 28
#define CID_ffi_catalog_union_Req 29
#define CID_tools_Name 30
#define CID_tools_Up 31
#define CID_tools_Here 32
#define CID_ffi_path_policy_Req 33
#define CID_ffi_tiny_Req 34
#define CID_catalog_union_Ent 35
#define CID_path_policy_Pol 36
#define CID_path_policy_Res 37
#define CID_wire_Dig 38
#define CID_wire_Comma 39
#define CID_wire_Other 40
#define CID_path_policy_Tree 41
#define CID_path_policy_Dir 42
#define CID_path_policy_Named 43
#define CID_path_policy_Judged 44
#define CID_gateway_width_Lay 45
#define CID_tiny_Use 46
#define CID_tiny_Unavailable 47
#define CID_catalog_union_TNil 48
#define CID_catalog_union_TNode 49
#define CID_path_policy_Inside 50
#define CID_path_policy_Outside 51
#define CID_path_policy_Protected 52
#define CID_path_policy_Secret 53
#define CID_gateway_width_Display 54
#define CID_gateway_width_Chars 55
#define CID_wire_flat_Start 56
#define CID_wire_flat_Mid 57
#define CID_IO_args 58
#define CID_IO_print 59
#define FID_tools_elem 0
#define FID_tools_elem_k6 1
#define FID_path_policy_parent_is 2
#define FID_gateway_width_cell_sum 3
#define FID_gateway_width_cell_sum_k9 4
#define FID_ffi_path_policy_rules_of 5
#define FID_ffi_path_policy_rules_of_k12 6
#define FID_path_policy_longer 7
#define FID_path_policy_longer_k14 8
#define FID_path_policy_longer_k15 9
#define FID_path_policy_strip 10
#define FID_path_policy_strip_k17 11
#define FID_path_policy_strip_k18 12
#define FID_path_policy_covers 13
#define FID_path_policy_covers_k20 14
#define FID_path_policy_covers_k21 15
#define FID_wire_put_str_go 16
#define FID_wire_put_str_go_k25 17
#define FID_ffi_path_policy_get_req_rules 18
#define FID_path_policy_entries 19
#define FID_path_policy_entries_k32 20
#define FID_path_policy_entries_k33 21
#define FID_path_policy_below 22
#define FID_path_policy_any_covers 23
#define FID_path_policy_any_covers_k37 24
#define FID_path_policy_any_covers_k38 25
#define FID_gateway_width_pads_at 26
#define FID_gateway_width_pads_at_k42 27
#define FID_gateway_width_pads_at_k43 28
#define FID_gateway_width_get_w 29
#define FID_wire_take 30
#define FID_wire_take_k46 31
#define FID_wire_put_str 32
#define FID_wire_put_str_k48 33
#define FID_tools_ids_eq 34
#define FID_tools_ids_eq_k56 35
#define FID_path_policy_under 36
#define FID_path_policy_under_k60 37
#define FID_path_policy_under_k61 38
#define FID_path_policy_root_of 39
#define FID_path_policy_root_of_k64 40
#define FID_path_policy_root_of_k65 41
#define FID_path_policy_root_of_k66 42
#define FID_path_policy_protects 43
#define FID_path_policy_protects_k68 44
#define FID_path_policy_protects_k69 45
#define FID_path_policy_protects_k70 46
#define FID_path_policy_protects_k71 47
#define FID_path_policy_protects_k72 48
#define FID_path_policy_protects_k73 49
#define FID_tiny_elem 50
#define FID_tiny_elem_k83 51
#define FID_gateway_width_pads_row 52
#define FID_List_length 53
#define FID_List_length_k88 54
#define FID_gateway_width_col_w 55
#define FID_gateway_width_col_w_k90 56
#define FID_gateway_width_col_w_k91 57
#define FID_wire_flat_one 58
#define FID_wire_flat_one_k93 59
#define FID_wire_value 60
#define FID_wire_value_k97 61
#define FID_path_policy_any_ancestor 62
#define FID_path_policy_any_ancestor_k109 63
#define FID_path_policy_any_ancestor_k110 64
#define FID_path_policy_any_ancestor_k111 65
#define FID_path_policy_any_under 66
#define FID_path_policy_any_under_k114 67
#define FID_path_policy_any_under_k115 68
#define FID_path_policy_class_of 69
#define FID_path_policy_class_of_k117 70
#define FID_path_policy_class_of_k118 71
#define FID_path_policy_class_of_k119 72
#define FID_catalog_union_put 73
#define FID_catalog_union_put_k134 74
#define FID_catalog_union_put_k135 75
#define FID_catalog_union_put_k136 76
#define FID_catalog_union_put_k137 77
#define FID_wire_put_list_go_0 78
#define FID_wire_put_list_go_0_k140 79
#define FID_tiny_up_at 80
#define FID_tiny_pick_go 81
#define FID_tiny_pick_go_k145 82
#define FID_wire_flat_fold 83
#define FID_wire_flat_fold_k147 84
#define FID_ffi_gateway_width_cells 85
#define FID_ffi_gateway_width_cells_k150 86
#define FID_gateway_width_pads_all 87
#define FID_gateway_width_pads_all_k152 88
#define FID_gateway_width_pads_all_k153 89
#define FID_gateway_width_cols 90
#define FID_gateway_width_cols_k155 91
#define FID_gateway_width_cols_k156 92
#define FID_gateway_width_widths 93
#define FID_gateway_width_widths_k158 94
#define FID_gateway_width_widths_k159 95
#define FID_wire_flat_flat 96
#define FID_wire_flat_flat_k161 97
#define FID_ffi_gateway_width_put_ns 98
#define FID_wire_cdig_go 99
#define FID_wire_cdig_go_k165 100
#define FID_wire_get_nat_go 101
#define FID_wire_get_nat_go_k168 102
#define FID_wire_get_nat_go_k169 103
#define FID_wire_get_nat_end 104
#define FID_wire_get_nat_end_k171 105
#define FID_wire_get_str 106
#define FID_wire_get_str_k176 107
#define FID_path_policy_holds_at 108
#define FID_path_policy_holds_at_k189 109
#define FID_path_policy_holds_at_k190 110
#define FID_path_policy_class_res 111
#define FID_path_policy_class_res_k192 112
#define FID_wire_get_list_go_0 113
#define FID_wire_get_list_go_0_k199 114
#define FID_wire_get_list_go_0_k200 115
#define FID_ffi_catalog_union_ents_of 116
#define FID_ffi_catalog_union_ents_of_k202 117
#define FID_catalog_union_extra_t 118
#define FID_catalog_union_extra_t_k206 119
#define FID_catalog_union_bundled_t 120
#define FID_catalog_union_bundled_t_k208 121
#define FID_List_append 122
#define FID_List_append_k210 123
#define FID_catalog_union_tab 124
#define FID_catalog_union_tab_k212 125
#define FID_wire_put_list_0 126
#define FID_wire_put_list_0_k215 127
#define FID_U32_show_go 128
#define FID_tiny_pick 129
#define FID_tiny_pick_k220 130
#define FID_wire_flat_unflat 131
#define FID_wire_flat_unflat_k223 132
#define FID_ffi_gateway_width_table 133
#define FID_ffi_gateway_width_table_k226 134
#define FID_ffi_gateway_width_table_k227 135
#define FID_gateway_width_layout 136
#define FID_gateway_width_layout_k229 137
#define FID_gateway_width_layout_k230 138
#define FID_gateway_width_layout_k231 139
#define FID_wire_tok 140
#define FID_wire_tok_k236 141
#define FID_path_policy_judge 142
#define FID_path_policy_judge_k253 143
#define FID_path_policy_judge_k254 144
#define FID_ffi_tools_segs 145
#define FID_ffi_tools_segs_k257 146
#define FID_catalog_union_fast 147
#define FID_catalog_union_fast_k268 148
#define FID_catalog_union_fast_k269 149
#define FID_catalog_union_fast_k270 150
#define FID_catalog_union_fast_k271 151
#define FID_ffi_catalog_union_ents 152
#define FID_ffi_catalog_union_ents_k273 153
#define FID_Nat_show_fin 154
#define FID_ffi_tiny_get_ids 155
#define FID_wire_peek 156
#define FID_wire_peek_k291 157
#define FID_wire_get_u32 158
#define FID_wire_get_u32_k296 159
#define FID_ffi_path_policy_get_ns 160
#define FID_wire_get_list_0 161
#define FID_wire_get_list_0_k318 162
#define FID_wire_get_list_0_k319 163
#define FID_U32_show 164
#define FID_Nat_show 165
#define FID_String_append 166
#define FID_String_append_k331 167
#define FID_ffi_tiny_get_req 168
#define FID_ffi_tiny_get_req_k333 169
#define FID_ffi_tiny_get_req_k334 170
#define FID_ffi_gateway_width_get_req 171
#define FID_ffi_gateway_width_get_req_k338 172
#define FID_ffi_gateway_width_get_req_k339 173
#define FID_wire_get_nat 174
#define FID_wire_get_nat_k346 175
#define FID_wire_get_nat_k347 176
#define FID_ffi_path_policy_get_req 177
#define FID_ffi_path_policy_get_req_k355 178
#define FID_ffi_path_policy_get_req_k356 179
#define FID_ffi_path_policy_get_req_k357 180
#define FID_ffi_path_policy_get_req_k358 181
#define FID_ffi_path_policy_get_req_k359 182
#define FID_ffi_path_policy_get_req_k360 183
#define FID_ffi_path_policy_get_req_k361 184
#define FID_ffi_path_policy_get_req_k362 185
#define FID_ffi_tools_get_req 186
#define FID_ffi_tools_get_req_k366 187
#define FID_ffi_tools_get_req_k367 188
#define FID_ffi_catalog_union_get_req 189
#define FID_ffi_catalog_union_get_req_k371 190
#define FID_ffi_catalog_union_get_req_k372 191
#define FID_ffi_catalog_union_get_req_k373 192
#define FID_ffi_catalog_union_get_req_k374 193
#define FID_ffi_echo_step 194
#define FID_ffi_echo_step_k381 195
#define FID_ffi_echo_step_k382 196
#define FID_ffi_echo_step_k383 197
#define FID_ffi_echo_open 198
#define FID_ffi_echo_open_k414 199
#define FID_ffi_echo_open_k415 200
#define FID_step_go 201
#define FID_step_go_k418 202
#define FID_ffi_go 203
#define FID_ffi_go_k421 204
#define FID_ffi_go_k422 205
#define FID_ffi_go_k423 206
#define FID_ffi_go_k424 207
#define FID_ffi_go_k425 208
#define FID_ffi_go_k426 209
#define FID_ffi_go_k427 210
#define FID_ffi_go_k428 211
#define FID_ffi_go_k429 212
#define FID_ffi_go_k430 213
#define FID_ffi_go_k431 214
#define FID_ffi_go_k432 215
#define FID_ffi_go_k433 216
#define FID_ffi_go_k434 217
#define FID_ffi_go_k435 218
#define FID_ffi_go_k436 219
#define FID_ffi_go_k437 220
#define FID_ffi_go_k438 221
#define FID_ffi_go_k439 222
#define FID_ffi_go_k440 223
#define FID_open_go 224
#define FID_open_go_k444 225
#define FID_step 226
#define FID_step_k446 227
#define FID_close 228
#define FID_ffi 229
#define FID_ffi_k450 230
#define FID_U32_read_go 231
#define FID_open 232
#define FID_open_k455 233
#define FID_cli_steps 234
#define FID_cli_steps_k457 235
#define FID_cli_steps_k458 236
#define FID_cli_steps_k459 237
#define FID_U32_read 238
#define FID_cli_print 239
#define FID_cli_print_c471 240
#define FID_cli_print_c472 241
#define FID_cli_print_c473 242
#define FID_cli_args 243
#define FID_cli_args_k475 244
#define FID_cli_args_k476 245
#define FID_cli_args_k477 246
#define FID_cli_args_k478 247
#define FID_IO_bind 248
#define FID_IO_bind_c482 249
#define FID_IO_bind_k483 250
#define FID_main 251
#define FID_main_c485 252
#define FID_main_c486 253
#define FID_main_k487 254
#define FID_main_c488 255
#define FID_IO_args 256
#define FID_IO_print 257
#define FID_IO_emit 258
#define FID_Clo_apply 259
#define FID_EXIT 260
#define FID_ENTER 261
CONSTV Fid FID_T[] = { { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 4, 1, 0, 1 }, { 2, 0, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 4, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 2, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 3, 0, 0, 1 }, { 3, 0, 0, 1 }, { 4, 1, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 6, 1, 0, 1 }, { 3, 1, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 4, 1, 0, 1 }, { 4, 2, 0, 1 }, { 1, 1, 0, 1 }, { 4, 0, 0, 1 }, { 6, 2, 0, 1 }, { 5, 1, 0, 1 }, { 5, 1, 0, 1 }, { 6, 1, 0, 1 }, { 3, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 1, 0, 1 }, { 3, 0, 0, 1 }, { 4, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 4, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 5, 1, 0, 1 }, { 6, 1, 0, 1 }, { 4, 2, 0, 1 }, { 16, 0, 0, 1 }, { 1, 1, 0, 1 }, { 1, 1, 0, 1 }, { 14, 1, 0, 1 }, { 14, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 2, 0, 1 }, { 2, 0, 0, 1 }, { 3, 0, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 5, 4, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 5, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 0, 0, 1 }, { 5, 2, 0, 1 }, { 5, 0, 0, 1 }, { 6, 3, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 0, 0, 1 }, { 5, 1, 0, 1 }, { 2, 1, 0, 1 }, { 5, 0, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 5, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 9, 2, 0, 1 }, { 3, 0, 0, 1 }, { 12, 1, 0, 1 }, { 2, 0, 0, 1 }, { 13, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 4, 4, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 5, 0, 0, 1 }, { 6, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 4, 1, 0, 1 }, { 4, 1, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 12, 1, 0, 1 }, { 4, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 3, 0, 1 }, { 6, 3, 0, 1 }, { 7, 2, 0, 1 }, { 8, 2, 0, 1 }, { 8, 2, 0, 1 }, { 9, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 4, 2, 0, 1 }, { 5, 2, 0, 1 }, { 4, 0, 0, 1 }, { 4, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 1, 0, 1 }, { 5, 0, 0, 1 }, { 4, 4, 0, 1 }, { 2, 0, 0, 1 }, { 4, 4, 0, 1 }, { 1, 1, 0, 1 }, { 1, 1, 0, 1 }, { 3, 3, 0, 1 }, { 1, 1, 0, 1 }, { 7, 7, 0, 1 }, { 2, 2, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 6, 3, 0, 1 }, { 7, 3, 0, 1 }, { 5, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 3, 0, 1 }, { 1, 1, 0, 1 }, { 2, 2, 0, 1 }, { 3, 1, 0, 1 }, { 2, 1, 0, 1 }, { 4, 4, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 4, 4, 0, 1 }, { 5, 0, 0, 1 }, { 5, 5, 0, 1 }, { 4, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 0, 0, 1 }, { 5, 5, 0, 1 }, { 6, 0, 0, 1 }, { 2, 1, 0, 1 }, { 7, 5, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 5, 2, 0, 1 }, { 1, 1, 0, 1 }, { 6, 5, 0, 1 }, { 1, 1, 0, 1 }, { 3, 0, 0, 1 }, { 3, 0, 0, 1 }, { 2, 1, 0, 1 }, { 0, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 } };
CONSTV Cid CID_T[] = { { 2, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 2, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 0, 1, 0 }, { 1, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 1, 1, 0 }, { 3, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 1, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 5, 0, 0 }, { 2, 0, 0 }, { 11, 1, 0 }, { 3, 1, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 1, 1, 0 }, { 1, 1, 0 }, { 1, 1, 0 }, { 2, 0, 0 }, { 2, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 14, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 2, 0, 0 } };
#define STAT_LEN 618

#define WL_RESW 7
#define BANGS   0

#define WL_BANK Term r0, r1, r2, r3, r4, r5, rp, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15;

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
    if ((N) <= 8) break; r8 = e.mem[(A) + 8]; \
    if ((N) <= 9) break; r9 = e.mem[(A) + 9]; \
    if ((N) <= 10) break; r10 = e.mem[(A) + 10]; \
    if ((N) <= 11) break; r11 = e.mem[(A) + 11]; \
    if ((N) <= 12) break; r12 = e.mem[(A) + 12]; \
    if ((N) <= 13) break; r13 = e.mem[(A) + 13]; \
    if ((N) <= 14) break; r14 = e.mem[(A) + 14]; \
    if ((N) <= 15) break; r15 = e.mem[(A) + 15]; \
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
    case 8: r8 = (X); \
      break; \
    case 9: r9 = (X); \
      break; \
    case 10: r10 = (X); \
      break; \
    case 11: r11 = (X); \
      break; \
    case 12: r12 = (X); \
      break; \
    case 13: r13 = (X); \
      break; \
    case 14: r14 = (X); \
      break; \
    case 15: r15 = (X); \
      break; \
  }

#define WL_SAVE(V) (V)[0] = r0; (V)[1] = r1; (V)[2] = r2; (V)[3] = r3; (V)[4] = r4; (V)[5] = r5; (V)[6] = r6;

#define WL_TAKE(V) r0 = (V)[0]; r1 = (V)[1]; r2 = (V)[2]; r3 = (V)[3]; r4 = (V)[4]; r5 = (V)[5]; r6 = (V)[6];

#define WL_SIG Env e, DEV Term* sp, u32 seq, u32 rn, Term r0, Term r1, Term r2, Term r3, Term r4, Term r5, Term rp, Term r6, Term r7, Term r8, Term r9, Term r10, Term r11, Term r12, Term r13, Term r14, Term r15

#define WL_ALL e, sp, seq, rn, r0, r1, r2, r3, r4, r5, rp, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15

#define WL_TABLE WL_X(FID_tools_elem) WL_X(FID_tools_elem_k6) WL_X(FID_path_policy_parent_is) WL_X(FID_gateway_width_cell_sum) WL_X(FID_gateway_width_cell_sum_k9) WL_X(FID_ffi_path_policy_rules_of) WL_X(FID_ffi_path_policy_rules_of_k12) WL_X(FID_path_policy_longer) WL_X(FID_path_policy_longer_k14) WL_X(FID_path_policy_longer_k15) WL_X(FID_path_policy_strip) WL_X(FID_path_policy_strip_k17) WL_X(FID_path_policy_strip_k18) WL_X(FID_path_policy_covers) WL_X(FID_path_policy_covers_k20) WL_X(FID_path_policy_covers_k21) WL_X(FID_wire_put_str_go) WL_X(FID_wire_put_str_go_k25) WL_X(FID_ffi_path_policy_get_req_rules) WL_X(FID_path_policy_entries) WL_X(FID_path_policy_entries_k32) WL_X(FID_path_policy_entries_k33) WL_X(FID_path_policy_below) WL_X(FID_path_policy_any_covers) WL_X(FID_path_policy_any_covers_k37) WL_X(FID_path_policy_any_covers_k38) WL_X(FID_gateway_width_pads_at) WL_X(FID_gateway_width_pads_at_k42) WL_X(FID_gateway_width_pads_at_k43) WL_X(FID_gateway_width_get_w) WL_X(FID_wire_take) WL_X(FID_wire_take_k46) WL_X(FID_wire_put_str) WL_X(FID_wire_put_str_k48) WL_X(FID_tools_ids_eq) WL_X(FID_tools_ids_eq_k56) WL_X(FID_path_policy_under) WL_X(FID_path_policy_under_k60) WL_X(FID_path_policy_under_k61) WL_X(FID_path_policy_root_of) WL_X(FID_path_policy_root_of_k64) WL_X(FID_path_policy_root_of_k65) WL_X(FID_path_policy_root_of_k66) WL_X(FID_path_policy_protects) WL_X(FID_path_policy_protects_k68) WL_X(FID_path_policy_protects_k69) WL_X(FID_path_policy_protects_k70) WL_X(FID_path_policy_protects_k71) WL_X(FID_path_policy_protects_k72) WL_X(FID_path_policy_protects_k73) WL_X(FID_tiny_elem) WL_X(FID_tiny_elem_k83) WL_X(FID_gateway_width_pads_row) WL_X(FID_List_length) WL_X(FID_List_length_k88) WL_X(FID_gateway_width_col_w) WL_X(FID_gateway_width_col_w_k90) WL_X(FID_gateway_width_col_w_k91) WL_X(FID_wire_flat_one) WL_X(FID_wire_flat_one_k93) WL_X(FID_wire_value) WL_X(FID_wire_value_k97) WL_X(FID_path_policy_any_ancestor) WL_X(FID_path_policy_any_ancestor_k109) WL_X(FID_path_policy_any_ancestor_k110) WL_X(FID_path_policy_any_ancestor_k111) WL_X(FID_path_policy_any_under) WL_X(FID_path_policy_any_under_k114) WL_X(FID_path_policy_any_under_k115) WL_X(FID_path_policy_class_of) WL_X(FID_path_policy_class_of_k117) WL_X(FID_path_policy_class_of_k118) WL_X(FID_path_policy_class_of_k119) WL_X(FID_catalog_union_put) WL_X(FID_catalog_union_put_k134) WL_X(FID_catalog_union_put_k135) WL_X(FID_catalog_union_put_k136) WL_X(FID_catalog_union_put_k137) WL_X(FID_wire_put_list_go_0) WL_X(FID_wire_put_list_go_0_k140) WL_X(FID_tiny_up_at) WL_X(FID_tiny_pick_go) WL_X(FID_tiny_pick_go_k145) WL_X(FID_wire_flat_fold) WL_X(FID_wire_flat_fold_k147) WL_X(FID_ffi_gateway_width_cells) WL_X(FID_ffi_gateway_width_cells_k150) WL_X(FID_gateway_width_pads_all) WL_X(FID_gateway_width_pads_all_k152) WL_X(FID_gateway_width_pads_all_k153) WL_X(FID_gateway_width_cols) WL_X(FID_gateway_width_cols_k155) WL_X(FID_gateway_width_cols_k156) WL_X(FID_gateway_width_widths) WL_X(FID_gateway_width_widths_k158) WL_X(FID_gateway_width_widths_k159) WL_X(FID_wire_flat_flat) WL_X(FID_wire_flat_flat_k161) WL_X(FID_ffi_gateway_width_put_ns) WL_X(FID_wire_cdig_go) WL_X(FID_wire_cdig_go_k165) WL_X(FID_wire_get_nat_go) WL_X(FID_wire_get_nat_go_k168) WL_X(FID_wire_get_nat_go_k169) WL_X(FID_wire_get_nat_end) WL_X(FID_wire_get_nat_end_k171) WL_X(FID_wire_get_str) WL_X(FID_wire_get_str_k176) WL_X(FID_path_policy_holds_at) WL_X(FID_path_policy_holds_at_k189) WL_X(FID_path_policy_holds_at_k190) WL_X(FID_path_policy_class_res) WL_X(FID_path_policy_class_res_k192) WL_X(FID_wire_get_list_go_0) WL_X(FID_wire_get_list_go_0_k199) WL_X(FID_wire_get_list_go_0_k200) WL_X(FID_ffi_catalog_union_ents_of) WL_X(FID_ffi_catalog_union_ents_of_k202) WL_X(FID_catalog_union_extra_t) WL_X(FID_catalog_union_extra_t_k206) WL_X(FID_catalog_union_bundled_t) WL_X(FID_catalog_union_bundled_t_k208) WL_X(FID_List_append) WL_X(FID_List_append_k210) WL_X(FID_catalog_union_tab) WL_X(FID_catalog_union_tab_k212) WL_X(FID_wire_put_list_0) WL_X(FID_wire_put_list_0_k215) WL_X(FID_U32_show_go) WL_X(FID_tiny_pick) WL_X(FID_tiny_pick_k220) WL_X(FID_wire_flat_unflat) WL_X(FID_wire_flat_unflat_k223) WL_X(FID_ffi_gateway_width_table) WL_X(FID_ffi_gateway_width_table_k226) WL_X(FID_ffi_gateway_width_table_k227) WL_X(FID_gateway_width_layout) WL_X(FID_gateway_width_layout_k229) WL_X(FID_gateway_width_layout_k230) WL_X(FID_gateway_width_layout_k231) WL_X(FID_wire_tok) WL_X(FID_wire_tok_k236) WL_X(FID_path_policy_judge) WL_X(FID_path_policy_judge_k253) WL_X(FID_path_policy_judge_k254) WL_X(FID_ffi_tools_segs) WL_X(FID_ffi_tools_segs_k257) WL_X(FID_catalog_union_fast) WL_X(FID_catalog_union_fast_k268) WL_X(FID_catalog_union_fast_k269) WL_X(FID_catalog_union_fast_k270) WL_X(FID_catalog_union_fast_k271) WL_X(FID_ffi_catalog_union_ents) WL_X(FID_ffi_catalog_union_ents_k273) WL_X(FID_Nat_show_fin) WL_X(FID_ffi_tiny_get_ids) WL_X(FID_wire_peek) WL_X(FID_wire_peek_k291) WL_X(FID_wire_get_u32) WL_X(FID_wire_get_u32_k296) WL_X(FID_ffi_path_policy_get_ns) WL_X(FID_wire_get_list_0) WL_X(FID_wire_get_list_0_k318) WL_X(FID_wire_get_list_0_k319) WL_X(FID_U32_show) WL_X(FID_Nat_show) WL_X(FID_String_append) WL_X(FID_String_append_k331) WL_X(FID_ffi_tiny_get_req) WL_X(FID_ffi_tiny_get_req_k333) WL_X(FID_ffi_tiny_get_req_k334) WL_X(FID_ffi_gateway_width_get_req) WL_X(FID_ffi_gateway_width_get_req_k338) WL_X(FID_ffi_gateway_width_get_req_k339) WL_X(FID_wire_get_nat) WL_X(FID_wire_get_nat_k346) WL_X(FID_wire_get_nat_k347) WL_X(FID_ffi_path_policy_get_req) WL_X(FID_ffi_path_policy_get_req_k355) WL_X(FID_ffi_path_policy_get_req_k356) WL_X(FID_ffi_path_policy_get_req_k357) WL_X(FID_ffi_path_policy_get_req_k358) WL_X(FID_ffi_path_policy_get_req_k359) WL_X(FID_ffi_path_policy_get_req_k360) WL_X(FID_ffi_path_policy_get_req_k361) WL_X(FID_ffi_path_policy_get_req_k362) WL_X(FID_ffi_tools_get_req) WL_X(FID_ffi_tools_get_req_k366) WL_X(FID_ffi_tools_get_req_k367) WL_X(FID_ffi_catalog_union_get_req) WL_X(FID_ffi_catalog_union_get_req_k371) WL_X(FID_ffi_catalog_union_get_req_k372) WL_X(FID_ffi_catalog_union_get_req_k373) WL_X(FID_ffi_catalog_union_get_req_k374) WL_X(FID_ffi_echo_step) WL_X(FID_ffi_echo_step_k381) WL_X(FID_ffi_echo_step_k382) WL_X(FID_ffi_echo_step_k383) WL_X(FID_ffi_echo_open) WL_X(FID_ffi_echo_open_k414) WL_X(FID_ffi_echo_open_k415) WL_X(FID_step_go) WL_X(FID_step_go_k418) WL_X(FID_ffi_go) WL_X(FID_ffi_go_k421) WL_X(FID_ffi_go_k422) WL_X(FID_ffi_go_k423) WL_X(FID_ffi_go_k424) WL_X(FID_ffi_go_k425) WL_X(FID_ffi_go_k426) WL_X(FID_ffi_go_k427) WL_X(FID_ffi_go_k428) WL_X(FID_ffi_go_k429) WL_X(FID_ffi_go_k430) WL_X(FID_ffi_go_k431) WL_X(FID_ffi_go_k432) WL_X(FID_ffi_go_k433) WL_X(FID_ffi_go_k434) WL_X(FID_ffi_go_k435) WL_X(FID_ffi_go_k436) WL_X(FID_ffi_go_k437) WL_X(FID_ffi_go_k438) WL_X(FID_ffi_go_k439) WL_X(FID_ffi_go_k440) WL_X(FID_open_go) WL_X(FID_open_go_k444) WL_X(FID_step) WL_X(FID_step_k446) WL_X(FID_close) WL_X(FID_ffi) WL_X(FID_ffi_k450) WL_X(FID_U32_read_go) WL_X(FID_open) WL_X(FID_open_k455) WL_X(FID_cli_steps) WL_X(FID_cli_steps_k457) WL_X(FID_cli_steps_k458) WL_X(FID_cli_steps_k459) WL_X(FID_U32_read) WL_X(FID_cli_print) WL_X(FID_cli_print_c471) WL_X(FID_cli_print_c472) WL_X(FID_cli_print_c473) WL_X(FID_cli_args) WL_X(FID_cli_args_k475) WL_X(FID_cli_args_k476) WL_X(FID_cli_args_k477) WL_X(FID_cli_args_k478) WL_X(FID_IO_bind) WL_X(FID_IO_bind_c482) WL_X(FID_IO_bind_k483) WL_X(FID_main) WL_X(FID_main_c485) WL_X(FID_main_c486) WL_X(FID_main_k487) WL_X(FID_main_c488) WL_X(FID_IO_args) WL_X(FID_IO_print) WL_X(FID_IO_emit) WL_X(FID_Clo_apply) WL_X(FID_EXIT)
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

CONSTV u64 STAT_IMG[] = { 116ull, term_pak(CID_SNil, 0), 115ull, term_ctr(CID_SCon, STAT_OFF + 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 2), 117ull, term_ctr(CID_SCon, STAT_OFF + 4), 113ull, term_ctr(CID_SCon, STAT_OFF + 6), 101ull, term_ctr(CID_SCon, STAT_OFF + 8), 114ull, term_ctr(CID_SCon, STAT_OFF + 10), 32ull, term_ctr(CID_SCon, STAT_OFF + 12), 101ull, term_ctr(CID_SCon, STAT_OFF + 14), 114ull, term_ctr(CID_SCon, STAT_OFF + 16), 105ull, term_ctr(CID_SCon, STAT_OFF + 18), 119ull, term_ctr(CID_SCon, STAT_OFF + 20), 32ull, term_ctr(CID_SCon, STAT_OFF + 22), 100ull, term_ctr(CID_SCon, STAT_OFF + 24), 101ull, term_ctr(CID_SCon, STAT_OFF + 26), 109ull, term_ctr(CID_SCon, STAT_OFF + 28), 114ull, term_ctr(CID_SCon, STAT_OFF + 30), 111ull, term_ctr(CID_SCon, STAT_OFF + 32), 102ull, term_ctr(CID_SCon, STAT_OFF + 34), 108ull, term_ctr(CID_SCon, STAT_OFF + 36), 97ull, term_ctr(CID_SCon, STAT_OFF + 38), 109ull, term_ctr(CID_SCon, STAT_OFF + 40), 57ull, term_pak(CID_Nil, 0), 56ull, term_ctr(CID_Con, STAT_OFF + 44), 55ull, term_ctr(CID_Con, STAT_OFF + 46), 54ull, term_ctr(CID_Con, STAT_OFF + 48), 53ull, term_ctr(CID_Con, STAT_OFF + 50), 52ull, term_ctr(CID_Con, STAT_OFF + 52), 51ull, term_ctr(CID_Con, STAT_OFF + 54), 50ull, term_ctr(CID_Con, STAT_OFF + 56), 49ull, term_ctr(CID_Con, STAT_OFF + 58), 48ull, term_ctr(CID_Con, STAT_OFF + 60), 0, term_pak(CID_Nil, 0), 48ull, term_pak(CID_SNil, 0), 114ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 68), 118ull, term_ctr(CID_SCon, STAT_OFF + 70), 111ull, term_ctr(CID_SCon, STAT_OFF + 72), 32ull, term_ctr(CID_SCon, STAT_OFF + 74), 116ull, term_ctr(CID_SCon, STAT_OFF + 76), 102ull, term_ctr(CID_SCon, STAT_OFF + 78), 101ull, term_ctr(CID_SCon, STAT_OFF + 80), 108ull, term_ctr(CID_SCon, STAT_OFF + 82), 32ull, term_ctr(CID_SCon, STAT_OFF + 84), 116ull, term_ctr(CID_SCon, STAT_OFF + 86), 117ull, term_ctr(CID_SCon, STAT_OFF + 88), 112ull, term_ctr(CID_SCon, STAT_OFF + 90), 110ull, term_ctr(CID_SCon, STAT_OFF + 92), 105ull, term_ctr(CID_SCon, STAT_OFF + 94), 32ull, term_ctr(CID_SCon, STAT_OFF + 96), 58ull, term_ctr(CID_SCon, STAT_OFF + 98), 121ull, term_ctr(CID_SCon, STAT_OFF + 100), 110ull, term_ctr(CID_SCon, STAT_OFF + 102), 105ull, term_ctr(CID_SCon, STAT_OFF + 104), 116ull, term_ctr(CID_SCon, STAT_OFF + 106), 104ull, term_ctr(CID_SCon, STAT_OFF + 100), 116ull, term_ctr(CID_SCon, STAT_OFF + 110), 100ull, term_ctr(CID_SCon, STAT_OFF + 112), 105ull, term_ctr(CID_SCon, STAT_OFF + 114), 119ull, term_ctr(CID_SCon, STAT_OFF + 116), 95ull, term_ctr(CID_SCon, STAT_OFF + 118), 121ull, term_ctr(CID_SCon, STAT_OFF + 120), 97ull, term_ctr(CID_SCon, STAT_OFF + 122), 119ull, term_ctr(CID_SCon, STAT_OFF + 124), 101ull, term_ctr(CID_SCon, STAT_OFF + 126), 116ull, term_ctr(CID_SCon, STAT_OFF + 128), 97ull, term_ctr(CID_SCon, STAT_OFF + 130), 103ull, term_ctr(CID_SCon, STAT_OFF + 132), 99ull, term_ctr(CID_SCon, STAT_OFF + 102), 105ull, term_ctr(CID_SCon, STAT_OFF + 136), 108ull, term_ctr(CID_SCon, STAT_OFF + 138), 111ull, term_ctr(CID_SCon, STAT_OFF + 140), 112ull, term_ctr(CID_SCon, STAT_OFF + 142), 95ull, term_ctr(CID_SCon, STAT_OFF + 144), 104ull, term_ctr(CID_SCon, STAT_OFF + 146), 116ull, term_ctr(CID_SCon, STAT_OFF + 148), 97ull, term_ctr(CID_SCon, STAT_OFF + 150), 112ull, term_ctr(CID_SCon, STAT_OFF + 152), 115ull, term_ctr(CID_SCon, STAT_OFF + 100), 108ull, term_ctr(CID_SCon, STAT_OFF + 156), 111ull, term_ctr(CID_SCon, STAT_OFF + 158), 111ull, term_ctr(CID_SCon, STAT_OFF + 160), 116ull, term_ctr(CID_SCon, STAT_OFF + 162), 110ull, term_ctr(CID_SCon, STAT_OFF + 100), 111ull, term_ctr(CID_SCon, STAT_OFF + 166), 105ull, term_ctr(CID_SCon, STAT_OFF + 168), 110ull, term_ctr(CID_SCon, STAT_OFF + 170), 117ull, term_ctr(CID_SCon, STAT_OFF + 172), 95ull, term_ctr(CID_SCon, STAT_OFF + 174), 103ull, term_ctr(CID_SCon, STAT_OFF + 176), 111ull, term_ctr(CID_SCon, STAT_OFF + 178), 108ull, term_ctr(CID_SCon, STAT_OFF + 180), 97ull, term_ctr(CID_SCon, STAT_OFF + 182), 116ull, term_ctr(CID_SCon, STAT_OFF + 184), 97ull, term_ctr(CID_SCon, STAT_OFF + 186), 99ull, term_ctr(CID_SCon, STAT_OFF + 188), 100ull, term_ctr(CID_SCon, STAT_OFF + 14), 101ull, term_ctr(CID_SCon, STAT_OFF + 192), 109ull, term_ctr(CID_SCon, STAT_OFF + 194), 114ull, term_ctr(CID_SCon, STAT_OFF + 196), 111ull, term_ctr(CID_SCon, STAT_OFF + 198), 102ull, term_ctr(CID_SCon, STAT_OFF + 200), 108ull, term_ctr(CID_SCon, STAT_OFF + 202), 97ull, term_ctr(CID_SCon, STAT_OFF + 204), 109ull, term_ctr(CID_SCon, STAT_OFF + 206), 32ull, term_ctr(CID_SCon, STAT_OFF + 208), 58ull, term_ctr(CID_SCon, STAT_OFF + 210), 121ull, term_ctr(CID_SCon, STAT_OFF + 212), 110ull, term_ctr(CID_SCon, STAT_OFF + 214), 105ull, term_ctr(CID_SCon, STAT_OFF + 216), 116ull, term_ctr(CID_SCon, STAT_OFF + 218), 104ull, term_ctr(CID_SCon, STAT_OFF + 212), 116ull, term_ctr(CID_SCon, STAT_OFF + 222), 100ull, term_ctr(CID_SCon, STAT_OFF + 224), 105ull, term_ctr(CID_SCon, STAT_OFF + 226), 119ull, term_ctr(CID_SCon, STAT_OFF + 228), 95ull, term_ctr(CID_SCon, STAT_OFF + 230), 121ull, term_ctr(CID_SCon, STAT_OFF + 232), 97ull, term_ctr(CID_SCon, STAT_OFF + 234), 119ull, term_ctr(CID_SCon, STAT_OFF + 236), 101ull, term_ctr(CID_SCon, STAT_OFF + 238), 116ull, term_ctr(CID_SCon, STAT_OFF + 240), 97ull, term_ctr(CID_SCon, STAT_OFF + 242), 103ull, term_ctr(CID_SCon, STAT_OFF + 244), 99ull, term_ctr(CID_SCon, STAT_OFF + 214), 105ull, term_ctr(CID_SCon, STAT_OFF + 248), 108ull, term_ctr(CID_SCon, STAT_OFF + 250), 111ull, term_ctr(CID_SCon, STAT_OFF + 252), 112ull, term_ctr(CID_SCon, STAT_OFF + 254), 95ull, term_ctr(CID_SCon, STAT_OFF + 256), 104ull, term_ctr(CID_SCon, STAT_OFF + 258), 116ull, term_ctr(CID_SCon, STAT_OFF + 260), 97ull, term_ctr(CID_SCon, STAT_OFF + 262), 112ull, term_ctr(CID_SCon, STAT_OFF + 264), 115ull, term_ctr(CID_SCon, STAT_OFF + 212), 108ull, term_ctr(CID_SCon, STAT_OFF + 268), 111ull, term_ctr(CID_SCon, STAT_OFF + 270), 111ull, term_ctr(CID_SCon, STAT_OFF + 272), 116ull, term_ctr(CID_SCon, STAT_OFF + 274), 110ull, term_ctr(CID_SCon, STAT_OFF + 212), 111ull, term_ctr(CID_SCon, STAT_OFF + 278), 105ull, term_ctr(CID_SCon, STAT_OFF + 280), 110ull, term_ctr(CID_SCon, STAT_OFF + 282), 117ull, term_ctr(CID_SCon, STAT_OFF + 284), 95ull, term_ctr(CID_SCon, STAT_OFF + 286), 103ull, term_ctr(CID_SCon, STAT_OFF + 288), 111ull, term_ctr(CID_SCon, STAT_OFF + 290), 108ull, term_ctr(CID_SCon, STAT_OFF + 292), 97ull, term_ctr(CID_SCon, STAT_OFF + 294), 116ull, term_ctr(CID_SCon, STAT_OFF + 296), 97ull, term_ctr(CID_SCon, STAT_OFF + 298), 99ull, term_ctr(CID_SCon, STAT_OFF + 300), 50ull, term_pak(CID_SNil, 0), 51ull, term_ctr(CID_SCon, STAT_OFF + 304), 85ull, term_ctr(CID_SCon, STAT_OFF + 306), 32ull, term_ctr(CID_SCon, STAT_OFF + 308), 108ull, term_ctr(CID_SCon, STAT_OFF + 310), 97ull, term_ctr(CID_SCon, STAT_OFF + 312), 109ull, term_ctr(CID_SCon, STAT_OFF + 314), 105ull, term_ctr(CID_SCon, STAT_OFF + 316), 99ull, term_ctr(CID_SCon, STAT_OFF + 318), 101ull, term_ctr(CID_SCon, STAT_OFF + 320), 100ull, term_ctr(CID_SCon, STAT_OFF + 322), 32ull, term_ctr(CID_SCon, STAT_OFF + 324), 97ull, term_ctr(CID_SCon, STAT_OFF + 326), 32ull, term_ctr(CID_SCon, STAT_OFF + 328), 115ull, term_ctr(CID_SCon, STAT_OFF + 330), 116ull, term_ctr(CID_SCon, STAT_OFF + 332), 110ull, term_ctr(CID_SCon, STAT_OFF + 334), 97ull, term_ctr(CID_SCon, STAT_OFF + 336), 119ull, term_ctr(CID_SCon, STAT_OFF + 338), 32ull, term_ctr(CID_SCon, STAT_OFF + 340), 110ull, term_ctr(CID_SCon, STAT_OFF + 342), 101ull, term_ctr(CID_SCon, STAT_OFF + 344), 112ull, term_ctr(CID_SCon, STAT_OFF + 346), 111ull, term_ctr(CID_SCon, STAT_OFF + 348), 32ull, term_ctr(CID_SCon, STAT_OFF + 350), 58ull, term_ctr(CID_SCon, STAT_OFF + 352), 111ull, term_ctr(CID_SCon, STAT_OFF + 354), 104ull, term_ctr(CID_SCon, STAT_OFF + 356), 99ull, term_ctr(CID_SCon, STAT_OFF + 358), 101ull, term_ctr(CID_SCon, STAT_OFF + 360), 32ull, term_ctr(CID_SCon, STAT_OFF + 362), 69ull, term_ctr(CID_SCon, STAT_OFF + 364), 32ull, term_pak(CID_SNil, 0), 100ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 370), 115ull, term_ctr(CID_SCon, STAT_OFF + 372), 117ull, term_ctr(CID_SCon, STAT_OFF + 374), 102ull, term_ctr(CID_SCon, STAT_OFF + 376), 101ull, term_ctr(CID_SCon, STAT_OFF + 378), 114ull, term_ctr(CID_SCon, STAT_OFF + 380), 32ull, term_ctr(CID_SCon, STAT_OFF + 382), 115ull, term_ctr(CID_SCon, STAT_OFF + 384), 97ull, term_ctr(CID_SCon, STAT_OFF + 386), 119ull, term_ctr(CID_SCon, STAT_OFF + 388), 32ull, term_ctr(CID_SCon, STAT_OFF + 390), 110ull, term_ctr(CID_SCon, STAT_OFF + 392), 101ull, term_ctr(CID_SCon, STAT_OFF + 394), 112ull, term_ctr(CID_SCon, STAT_OFF + 396), 111ull, term_ctr(CID_SCon, STAT_OFF + 398), 32ull, term_ctr(CID_SCon, STAT_OFF + 400), 101ull, term_ctr(CID_SCon, STAT_OFF + 402), 104ull, term_ctr(CID_SCon, STAT_OFF + 404), 116ull, term_ctr(CID_SCon, STAT_OFF + 406), 32ull, term_ctr(CID_SCon, STAT_OFF + 408), 58ull, term_ctr(CID_SCon, STAT_OFF + 410), 111ull, term_ctr(CID_SCon, STAT_OFF + 412), 104ull, term_ctr(CID_SCon, STAT_OFF + 414), 99ull, term_ctr(CID_SCon, STAT_OFF + 416), 101ull, term_ctr(CID_SCon, STAT_OFF + 418), 32ull, term_ctr(CID_SCon, STAT_OFF + 420), 69ull, term_ctr(CID_SCon, STAT_OFF + 422), 121ull, term_pak(CID_SNil, 0), 114ull, term_ctr(CID_SCon, STAT_OFF + 426), 116ull, term_ctr(CID_SCon, STAT_OFF + 428), 110ull, term_ctr(CID_SCon, STAT_OFF + 430), 101ull, term_ctr(CID_SCon, STAT_OFF + 432), 32ull, term_ctr(CID_SCon, STAT_OFF + 434), 110ull, term_ctr(CID_SCon, STAT_OFF + 436), 119ull, term_ctr(CID_SCon, STAT_OFF + 438), 111ull, term_ctr(CID_SCon, STAT_OFF + 440), 110ull, term_ctr(CID_SCon, STAT_OFF + 442), 107ull, term_ctr(CID_SCon, STAT_OFF + 444), 110ull, term_ctr(CID_SCon, STAT_OFF + 446), 117ull, term_ctr(CID_SCon, STAT_OFF + 448), 32ull, term_ctr(CID_SCon, STAT_OFF + 450), 69ull, term_ctr(CID_SCon, STAT_OFF + 452), 108ull, term_pak(CID_SNil, 0), 108ull, term_ctr(CID_SCon, STAT_OFF + 456), 97ull, term_ctr(CID_SCon, STAT_OFF + 458), 99ull, term_ctr(CID_SCon, STAT_OFF + 460), 110ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 464), 112ull, term_ctr(CID_SCon, STAT_OFF + 466), 111ull, term_ctr(CID_SCon, STAT_OFF + 468), 93ull, term_pak(CID_SNil, 0), 46ull, term_ctr(CID_SCon, STAT_OFF + 472), 46ull, term_ctr(CID_SCon, STAT_OFF + 474), 46ull, term_ctr(CID_SCon, STAT_OFF + 476), 62ull, term_ctr(CID_SCon, STAT_OFF + 478), 116ull, term_ctr(CID_SCon, STAT_OFF + 480), 110ull, term_ctr(CID_SCon, STAT_OFF + 482), 101ull, term_ctr(CID_SCon, STAT_OFF + 484), 118ull, term_ctr(CID_SCon, STAT_OFF + 486), 101ull, term_ctr(CID_SCon, STAT_OFF + 488), 60ull, term_ctr(CID_SCon, STAT_OFF + 490), 91ull, term_ctr(CID_SCon, STAT_OFF + 492), 32ull, term_ctr(CID_SCon, STAT_OFF + 494), 62ull, term_ctr(CID_SCon, STAT_OFF + 496), 116ull, term_ctr(CID_SCon, STAT_OFF + 498), 117ull, term_ctr(CID_SCon, STAT_OFF + 500), 112ull, term_ctr(CID_SCon, STAT_OFF + 502), 110ull, term_ctr(CID_SCon, STAT_OFF + 504), 105ull, term_ctr(CID_SCon, STAT_OFF + 506), 60ull, term_ctr(CID_SCon, STAT_OFF + 508), 32ull, term_ctr(CID_SCon, STAT_OFF + 510), 62ull, term_ctr(CID_SCon, STAT_OFF + 512), 121ull, term_ctr(CID_SCon, STAT_OFF + 514), 114ull, term_ctr(CID_SCon, STAT_OFF + 516), 116ull, term_ctr(CID_SCon, STAT_OFF + 518), 110ull, term_ctr(CID_SCon, STAT_OFF + 520), 101ull, term_ctr(CID_SCon, STAT_OFF + 522), 60ull, term_ctr(CID_SCon, STAT_OFF + 524), 32ull, term_ctr(CID_SCon, STAT_OFF + 526), 110ull, term_ctr(CID_SCon, STAT_OFF + 528), 101ull, term_ctr(CID_SCon, STAT_OFF + 530), 112ull, term_ctr(CID_SCon, STAT_OFF + 532), 111ull, term_ctr(CID_SCon, STAT_OFF + 534), 32ull, term_ctr(CID_SCon, STAT_OFF + 536), 101ull, term_ctr(CID_SCon, STAT_OFF + 538), 114ull, term_ctr(CID_SCon, STAT_OFF + 540), 111ull, term_ctr(CID_SCon, STAT_OFF + 542), 99ull, term_ctr(CID_SCon, STAT_OFF + 544), 32ull, term_ctr(CID_SCon, STAT_OFF + 546), 124ull, term_ctr(CID_SCon, STAT_OFF + 548), 32ull, term_ctr(CID_SCon, STAT_OFF + 550), 62ull, term_ctr(CID_SCon, STAT_OFF + 552), 116ull, term_ctr(CID_SCon, STAT_OFF + 554), 117ull, term_ctr(CID_SCon, STAT_OFF + 556), 112ull, term_ctr(CID_SCon, STAT_OFF + 558), 110ull, term_ctr(CID_SCon, STAT_OFF + 560), 105ull, term_ctr(CID_SCon, STAT_OFF + 562), 60ull, term_ctr(CID_SCon, STAT_OFF + 564), 32ull, term_ctr(CID_SCon, STAT_OFF + 566), 62ull, term_ctr(CID_SCon, STAT_OFF + 568), 121ull, term_ctr(CID_SCon, STAT_OFF + 570), 114ull, term_ctr(CID_SCon, STAT_OFF + 572), 116ull, term_ctr(CID_SCon, STAT_OFF + 574), 110ull, term_ctr(CID_SCon, STAT_OFF + 576), 101ull, term_ctr(CID_SCon, STAT_OFF + 578), 60ull, term_ctr(CID_SCon, STAT_OFF + 580), 32ull, term_ctr(CID_SCon, STAT_OFF + 582), 108ull, term_ctr(CID_SCon, STAT_OFF + 584), 108ull, term_ctr(CID_SCon, STAT_OFF + 586), 97ull, term_ctr(CID_SCon, STAT_OFF + 588), 99ull, term_ctr(CID_SCon, STAT_OFF + 590), 32ull, term_ctr(CID_SCon, STAT_OFF + 592), 101ull, term_ctr(CID_SCon, STAT_OFF + 594), 114ull, term_ctr(CID_SCon, STAT_OFF + 596), 111ull, term_ctr(CID_SCon, STAT_OFF + 598), 99ull, term_ctr(CID_SCon, STAT_OFF + 600), 32ull, term_ctr(CID_SCon, STAT_OFF + 602), 58ull, term_ctr(CID_SCon, STAT_OFF + 604), 101ull, term_ctr(CID_SCon, STAT_OFF + 606), 103ull, term_ctr(CID_SCon, STAT_OFF + 608), 97ull, term_ctr(CID_SCon, STAT_OFF + 610), 115ull, term_ctr(CID_SCon, STAT_OFF + 612), 117ull, term_ctr(CID_SCon, STAT_OFF + 614) };

INLINE Term spin_0(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _rest_0 = r1;
  WL_SPIN
    if (term_aux(_rest_0) == CID_Nil) {
      o[0] = 1;
      o[1] = 2;
      o[2] = _n_0;
    } else {
      Term _fb_2[2];
      u64 _sp_2 = ctr_take(e, _rest_0, 2, _fb_2);
      Term _f_4 = _fb_2[0];
      Term _f_5 = _fb_2[1];
      term_sink(e, _f_5);
      o[0] = 0;
      o[1] = 0;
      o[2] = 0;
      spare_free(e, cls_fit(2), _sp_2);
    }
  break;
  }
  return 1;
}

INLINE Term spin_2(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  WL_SPIN
    if (_c_0 == 1) {
      o[0] = 1;
    } else {
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_1(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_2(e, _o_0, ((_a_0 > _b_0) + (_a_0 >= _b_0))) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_3(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _xs_0 = r0;
  WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      o[0] = 0;
      o[1] = 0;
      o[2] = 0;
    } else {
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _xs_0, 2, _fb_1);
      Term _f_3 = _fb_1[0];
      Term _f_4 = _fb_1[1];
      if (_f_3 == 0) {
        o[0] = 1;
        o[1] = 0;
        o[2] = _f_4;
        spare_free(e, cls_fit(2), _sp_1);
      } else if (_f_3 == 1) {
        o[0] = 1;
        o[1] = 1;
        o[2] = _f_4;
        spare_free(e, cls_fit(2), _sp_1);
      } else if (_f_3 == 2) {
        if (term_aux(_f_4) == CID_Nil) {
          o[0] = 0;
          o[1] = 0;
          o[2] = 0;
          spare_free(e, cls_fit(2), _sp_1);
        } else {
          Term _fb_2[2];
          u64 _sp_2 = ctr_take(e, _f_4, 2, _fb_2);
          Term _f_5 = _fb_2[0];
          Term _f_6 = _fb_2[1];
          Term _o_0[3];
          if (spin_0(e, _o_0, _f_5, _f_6) == 0) {
            return 0;
          }
          o[0] = (u32)_o_0[0];
          o[1] = (u32)_o_0[1];
          o[2] = _o_0[2];
          spare_free(e, cls_fit(2), _sp_2);
          spare_free(e, cls_fit(2), _sp_1);
        }
      } else {
        Term _c_0 = (_f_3 - 3);
        term_sink(e, _f_4);
        o[0] = 0;
        o[1] = 0;
        o[2] = 0;
        spare_free(e, cls_fit(2), _sp_1);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_4(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, Term r4) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  u32 _m_1 = r1;
  Term _m_2 = r2;
  u32 _ms_0 = r3;
  Term _ms_1 = r4;
  WL_SPIN
    if (_m_0 == 1) {
      if (_ms_0 == 1) {
        Term _b_0 = 0;
        if (_m_1 == 0) {
          u64 _nd_0 = heap_alloc(e, cls_fit(1));
          e.mem[_nd_0 + 0] = rfc_seal(e, _m_2);
          _b_0 = term_ctr(CID_path_policy_Tree, _nd_0);
        } else if (_m_1 == 1) {
          u64 _nd_1 = heap_alloc(e, cls_fit(1));
          e.mem[_nd_1 + 0] = rfc_seal(e, _m_2);
          _b_0 = term_ctr(CID_path_policy_Dir, _nd_1);
        } else {
          u64 _nd_2 = heap_alloc(e, cls_fit(1));
          e.mem[_nd_2 + 0] = rfc_seal(e, _m_2);
          _b_0 = term_ctr(CID_path_policy_Named, _nd_2);
        }
        u64 _nd_3 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_3 + 0] = rfc_seal(e, _b_0);
        e.mem[_nd_3 + 1] = rfc_seal(e, _ms_1);
        o[0] = 1;
        o[1] = term_ctr(CID_Con, _nd_3);
      } else {
        term_sink(e, _m_2);
        o[0] = 0;
        o[1] = 0;
      }
    } else {
      if (_ms_0 == 1) {
        term_sink(e, _ms_1);
        o[0] = 0;
        o[1] = 0;
      } else {
        o[0] = 0;
        o[1] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_5(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _b_longer_0 = r0;
  Term _a_3 = r1;
  Term _b_3 = r2;
  WL_SPIN
    if (_b_longer_0 == 1) {
      term_sink(e, _a_3);
      o[0] = _b_3;
    } else {
      term_sink(e, _b_3);
      o[0] = _a_3;
    }
  break;
  }
  return 1;
}

INLINE Term spin_6(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _hit_0 = r0;
  Term _x_0 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    if (_hit_0 == 1) {
      term_sink(e, _rest_0);
      o[0] = term_pak(CID_Nil, 0);
    } else {
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_1 + 1] = rfc_seal(e, _rest_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_7(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
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

INLINE Term spin_10(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  Term _p_1 = r1;
  WL_SPIN
    o[0] = _p_0;
  break;
  }
  return 1;
}

INLINE Term spin_9(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _a_1 = (_b_0 == 0 ? 0 : _a_0 / _b_0);
    Term _a_2 = (_b_0 == 0 ? _a_0 : _a_0 % _b_0);
    Term _o_0[1];
    if (spin_10(e, _o_0, _a_1, _a_2) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_12(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_2 = r0;
  Term _p_3 = r1;
  WL_SPIN
    o[0] = _p_3;
  break;
  }
  return 1;
}

INLINE Term spin_11(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_3 = r0;
  Term _b_1 = r1;
  WL_SPIN
    Term _a_4 = (_b_1 == 0 ? 0 : _a_3 / _b_1);
    Term _a_5 = (_b_1 == 0 ? _a_3 : _a_3 % _b_1);
    Term _o_2[1];
    if (spin_12(e, _o_2, _a_4, _a_5) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_13(Env e, THR Term* o, Term r0) {
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

INLINE Term spin_14(Env e, THR Term* o, Term r0, Term r1, Term r2) {
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
        Term _v_3 = 0;
        Term _o_5[1];
        if (spin_9(e, _o_5, _m_0, 10ull) == 0) {
          return 0;
        }
        _v_3 = _o_5[0];
        u32 _v_4 = 0;
        Term _v_5 = 0;
        Term _o_6[1];
        if (spin_11(e, _o_6, _m_0, 10ull) == 0) {
          return 0;
        }
        _v_5 = _o_6[0];
        Term _o_7[1];
        if (spin_13(e, _o_7, _v_5) == 0) {
          return 0;
        }
        _v_4 = (u32)_o_7[0];
        u64 _nd_2 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_2 + 0] = rfc_seal(e, _v_4);
        e.mem[_nd_2 + 1] = rfc_seal(e, _acc_0);
        r0 = _f_0;
        r1 = _v_3;
        r2 = term_ctr(CID_SCon, _nd_2);
        _g_0 = r0;
        _n_1 = r1;
        _acc_0 = r2;
        WL_AGAIN(spin_14);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_8(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _rest_0 = r1;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_1[1];
    if (spin_9(e, _o_1, _n_0, 10ull) == 0) {
      return 0;
    }
    _v_0 = _o_1[0];
    u32 _v_1 = 0;
    Term _v_2 = 0;
    Term _o_3[1];
    if (spin_11(e, _o_3, _n_0, 10ull) == 0) {
      return 0;
    }
    _v_2 = _o_3[0];
    Term _o_4[1];
    if (spin_13(e, _o_4, _v_2) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_4[0];
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, 44ull);
    e.mem[_nd_0 + 1] = rfc_seal(e, _rest_0);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _v_1);
    e.mem[_nd_1 + 1] = rfc_seal(e, term_ctr(CID_SCon, _nd_0));
    Term _o_8[1];
    if (spin_14(e, _o_8, _n_0, _v_0, term_ctr(CID_SCon, _nd_1)) == 0) {
      return 0;
    }
    o[0] = _o_8[0];
  break;
  }
  return 1;
}

INLINE Term spin_15(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _st_3 = r0;
  Term _st_4 = r1;
  Term _st_5 = r2;
  WL_SPIN
    if (_st_3 == 0) {
      o[0] = term_pak(CID_Nil, 0);
    } else {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _st_4);
      e.mem[_nd_0 + 1] = rfc_seal(e, _st_5);
      o[0] = term_ctr(CID_Con, _nd_0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_16(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
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

INLINE Term spin_17(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _r_0 = r0;
  Term _r_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_8(e, _o_0, _r_0, _r_1) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_18(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, u32 r4, Term r5, Term r6, u32 r7, Term r8) {
  u32 wpoll = 0;
  u32 _mro_0 = r0;
  Term _mro_1 = r1;
  u32 _mru_0 = r2;
  Term _mru_1 = r3;
  u32 _mse_0 = r4;
  Term _mse_1 = r5;
  Term _at_5 = r6;
  u32 _l_0 = r7;
  Term _s_0 = r8;
  WL_SPIN
    if (_mro_0 == 0) {
      term_sink(e, _mru_1);
      term_sink(e, _mse_1);
      term_sink(e, _at_5);
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
    } else {
      if (_mru_0 == 0) {
        term_sink(e, _mro_1);
        term_sink(e, _mse_1);
        term_sink(e, _at_5);
        term_sink(e, _s_0);
        o[0] = 1;
        o[1] = 0;
        o[2] = 0;
        o[3] = 0;
        o[4] = 0;
        o[5] = 0;
        o[6] = 0;
      } else {
        if (_mse_0 == 0) {
          term_sink(e, _mro_1);
          term_sink(e, _mru_1);
          term_sink(e, _at_5);
          term_sink(e, _s_0);
          o[0] = 1;
          o[1] = 0;
          o[2] = 0;
          o[3] = 0;
          o[4] = 0;
          o[5] = 0;
          o[6] = 0;
        } else {
          o[0] = 0;
          o[1] = _mro_1;
          o[2] = _mru_1;
          o[3] = _mse_1;
          o[4] = _at_5;
          o[5] = _l_0;
          o[6] = _s_0;
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_19(Env e, THR Term* o, u32 r0, u32 r1) {
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

INLINE Term spin_20(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  Term _p_1 = r1;
  Term _p_2 = r2;
  WL_SPIN
    term_sink(e, _p_1);
    term_sink(e, _p_2);
    o[0] = _p_0;
  break;
  }
  return 1;
}

INLINE Term spin_21(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _p_3 = r0;
  Term _p_4 = r1;
  Term _p_5 = r2;
  WL_SPIN
    term_sink(e, _p_3);
    term_sink(e, _p_5);
    o[0] = _p_4;
  break;
  }
  return 1;
}

INLINE Term spin_22(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _p_6 = r0;
  Term _p_7 = r1;
  Term _p_8 = r2;
  WL_SPIN
    term_sink(e, _p_6);
    term_sink(e, _p_7);
    o[0] = _p_8;
  break;
  }
  return 1;
}

INLINE Term spin_23(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _k_1 = r0;
  WL_SPIN
    Term _a_0 = 1ull;
    Term _o_0[1];
    if (spin_9(e, _o_0, (_k_1 < _a_0 ? 0 : _k_1 - _a_0), 2ull) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_24(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _k_2 = r0;
  WL_SPIN
    Term _o_2[1];
    if (spin_1(e, _o_2, _k_2, 0) == 0) {
      return 0;
    }
    o[0] = (u32)_o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_25(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _k_3 = r0;
  WL_SPIN
    Term _v_3 = 0;
    Term _a_1 = 1ull;
    Term _o_4[1];
    if (spin_11(e, _o_4, (_k_3 < _a_1 ? 0 : _k_3 - _a_1), 2ull) == 0) {
      return 0;
    }
    _v_3 = _o_4[0];
    Term _o_5[1];
    if (spin_1(e, _o_5, _v_3, 1ull) == 0) {
      return 0;
    }
    o[0] = (u32)_o_5[0];
  break;
  }
  return 1;
}

INLINE Term spin_26(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, u32 r4) {
  u32 wpoll = 0;
  u32 _o_1 = r0;
  Term _o_2 = r1;
  u32 _c_11 = r2;
  Term _c_12 = r3;
  u32 _same_0 = r4;
  WL_SPIN
    if (_o_1 == 1) {
      o[0] = 1;
      o[1] = _o_2;
    } else {
      if (_same_0 == 1) {
        o[0] = _c_11;
        o[1] = _c_12;
      } else {
        o[0] = 0;
        o[1] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_27(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _n_1 = r0;
  u32 _st_0 = r1;
  Term _st_1 = r2;
  Term _st_2 = r3;
  WL_SPIN
    if (_n_1 == 0) {
      Term _v_0 = 0;
      Term _o_0[1];
      if (spin_15(e, _o_0, _st_0, _st_1, _st_2) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      o[0] = 1;
      o[1] = 1;
      o[2] = term_pak(CID_Nil, 0);
      o[3] = _v_0;
    } else {
      Term _x_0 = (_n_1 - 1);
      if (_st_0 == 0) {
        o[0] = 0;
        o[1] = 0;
        o[2] = 0;
        o[3] = 0;
      } else {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _x_0);
        e.mem[_nd_0 + 1] = rfc_seal(e, _st_1);
        o[0] = 1;
        o[1] = 1;
        o[2] = term_ctr(CID_Con, _nd_0);
        o[3] = _st_2;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_28(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _b_3 = r0;
  Term _rest_0 = r1;
  WL_SPIN
    if (_b_3 == 1) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, 84ull);
      e.mem[_nd_0 + 1] = rfc_seal(e, _rest_0);
      o[0] = term_ctr(CID_SCon, _nd_0);
    } else {
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, 70ull);
      e.mem[_nd_1 + 1] = rfc_seal(e, _rest_0);
      o[0] = term_ctr(CID_SCon, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_29(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _x_3 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    Term _o_1[1];
    if (spin_8(e, _o_1, ((u64)_x_3), _rest_1) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_31(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _text_0 = r0;
  WL_SPIN
    u64 _nd_2 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_2 + 0] = rfc_seal(e, 32ull);
    e.mem[_nd_2 + 1] = rfc_seal(e, _text_0);
    u64 _nd_3 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_3 + 0] = rfc_seal(e, 69ull);
    e.mem[_nd_3 + 1] = rfc_seal(e, term_ctr(CID_SCon, _nd_2));
    o[0] = term_ctr(CID_SCon, _nd_3);
  break;
  }
  return 1;
}

INLINE Term spin_30(Env e, THR Term* o) {
  u32 wpoll = 0;
  WL_SPIN
    Term _o_4[1];
    if (spin_31(e, _o_4, term_ctr(CID_SCon, STAT_OFF + 42)) == 0) {
      return 0;
    }
    o[0] = _o_4[0];
  break;
  }
  return 1;
}

INLINE Term spin_34(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _f_3 = r0;
  Term _s_2 = r1;
  WL_SPIN
    if (_f_3 == 1) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_2;
    } else {
      term_sink(e, _s_2);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_33(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _t_0 = r0;
  u32 _f_2 = r1;
  Term _s_1 = r2;
  WL_SPIN
    if (_t_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_1;
    } else {
      Term _o_0[3];
      if (spin_34(e, _o_0, _f_2, _s_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = (u32)_o_0[1];
      o[2] = _o_0[2];
    }
  break;
  }
  return 1;
}

INLINE Term spin_32(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_0 = r0;
  WL_SPIN
    if (term_aux(_s_0) == CID_SNil) {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_0, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _o_1[3];
      if (spin_33(e, _o_1, U32_BIN(_f_0, ==, 84ull), U32_BIN(_f_0, ==, 70ull), _f_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = (u32)_o_1[1];
      o[2] = _o_1[2];
      spare_free(e, cls_fit(2), _sp_0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_35(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  WL_SPIN
    if (_b_0 == 0) {
      o[0] = 1;
    } else {
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_36(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = 0;
    } else {
      term_sink(e, _m_1);
      o[0] = 1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_37(Env e, THR Term* o, u32 r0, u32 r1, u32 r2) {
  u32 wpoll = 0;
  u32 _sec_0 = r0;
  u32 _prot_0 = r1;
  u32 _inside_0 = r2;
  WL_SPIN
    if (_sec_0 == 1) {
      o[0] = 3;
    } else {
      if (_prot_0 == 1) {
        o[0] = 2;
      } else {
        if (_inside_0 == 1) {
          o[0] = 0;
        } else {
          o[0] = 1;
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_38(Env e, THR Term* o, Term r0, Term r1, u32 r2, u32 r3) {
  u32 wpoll = 0;
  Term _t_1 = r0;
  Term _k_1 = r1;
  u32 _z_0 = r2;
  u32 _odd_0 = r3;
  WL_SPIN
    if (term_aux(_t_1) == CID_catalog_union_TNil) {
      o[0] = 0;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
      o[7] = 0;
      o[8] = 0;
      o[9] = 0;
      o[10] = 0;
      o[11] = 0;
    } else {
      u64 _sp_0 = term_peek(e.mem, _t_1);
      u32 _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      Term _f_2 = e.mem[_sp_0 + 2];
      Term _f_3 = e.mem[_sp_0 + 3];
      u32 _f_4 = e.mem[_sp_0 + 4];
      Term _f_5 = e.mem[_sp_0 + 5];
      u32 _f_6 = e.mem[_sp_0 + 6];
      Term _f_7 = e.mem[_sp_0 + 7];
      u32 _f_8 = e.mem[_sp_0 + 8];
      Term _f_9 = e.mem[_sp_0 + 9];
      u32 _f_10 = e.mem[_sp_0 + 10];
      Term _f_11 = e.mem[_sp_0 + 11];
      Term _f_12 = e.mem[_sp_0 + 12];
      Term _f_13 = e.mem[_sp_0 + 13];
      if (_z_0 == 1) {
        o[0] = _f_0;
        o[1] = _f_1;
        o[2] = _f_2;
        o[3] = _f_3;
        o[4] = _f_4;
        o[5] = _f_5;
        o[6] = _f_6;
        o[7] = _f_7;
        o[8] = _f_8;
        o[9] = _f_9;
        o[10] = _f_10;
        o[11] = _f_11;
      } else {
        if (_odd_0 == 1) {
          Term _v_2 = 0;
          Term _o_2[1];
          if (spin_23(e, _o_2, _k_1) == 0) {
            return 0;
          }
          _v_2 = _o_2[0];
          u32 _v_3 = 0;
          Term _o_3[1];
          if (spin_24(e, _o_3, _v_2) == 0) {
            return 0;
          }
          _v_3 = (u32)_o_3[0];
          u32 _v_4 = 0;
          Term _o_4[1];
          if (spin_25(e, _o_4, _v_2) == 0) {
            return 0;
          }
          _v_4 = (u32)_o_4[0];
          r0 = _f_13;
          r1 = _v_2;
          r2 = _v_3;
          r3 = _v_4;
          _t_1 = r0;
          _k_1 = r1;
          _z_0 = r2;
          _odd_0 = r3;
          WL_AGAIN(spin_38);
        } else {
          Term _v_5 = 0;
          Term _o_5[1];
          if (spin_23(e, _o_5, _k_1) == 0) {
            return 0;
          }
          _v_5 = _o_5[0];
          u32 _v_6 = 0;
          Term _o_6[1];
          if (spin_24(e, _o_6, _v_5) == 0) {
            return 0;
          }
          _v_6 = (u32)_o_6[0];
          u32 _v_7 = 0;
          Term _o_7[1];
          if (spin_25(e, _o_7, _v_5) == 0) {
            return 0;
          }
          _v_7 = (u32)_o_7[0];
          r0 = _f_12;
          r1 = _v_5;
          r2 = _v_6;
          r3 = _v_7;
          _t_1 = r0;
          _k_1 = r1;
          _z_0 = r2;
          _odd_0 = r3;
          WL_AGAIN(spin_38);
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_39(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, u32 r5, Term r6, u32 r7, Term r8, u32 r9, Term r10, Term r11, Term r12, Term r13, u32 r14, Term r15, u32 r16, Term r17, u32 r18, Term r19, u32 r20, Term r21) {
  u32 wpoll = 0;
  Term _b_11 = r0;
  Term _b_12 = r1;
  Term _b_13 = r2;
  u32 _b_14 = r3;
  Term _b_15 = r4;
  u32 _b_16 = r5;
  Term _b_17 = r6;
  u32 _b_18 = r7;
  Term _b_19 = r8;
  u32 _b_20 = r9;
  Term _b_21 = r10;
  Term _c_0 = r11;
  Term _c_1 = r12;
  Term _c_2 = r13;
  u32 _c_3 = r14;
  Term _c_4 = r15;
  u32 _c_5 = r16;
  Term _c_6 = r17;
  u32 _c_7 = r18;
  Term _c_8 = r19;
  u32 _c_9 = r20;
  Term _c_10 = r21;
  WL_SPIN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_1(e, _o_0, _b_12, _c_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    u32 _v_1 = 0;
    Term _v_2 = 0;
    Term _o_1[2];
    if (spin_26(e, _o_1, _b_14, _b_15, _c_3, _c_4, _v_0) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_1[0];
    _v_2 = _o_1[1];
    u32 _v_3 = 0;
    Term _v_4 = 0;
    Term _o_2[2];
    if (spin_26(e, _o_2, _b_16, _b_17, _c_5, _c_6, _v_0) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_2[0];
    _v_4 = _o_2[1];
    u32 _v_5 = 0;
    Term _v_6 = 0;
    Term _o_3[2];
    if (spin_26(e, _o_3, _b_18, _b_19, _c_7, _c_8, _v_0) == 0) {
      return 0;
    }
    _v_5 = (u32)_o_3[0];
    _v_6 = _o_3[1];
    u32 _v_7 = 0;
    Term _v_8 = 0;
    Term _o_4[2];
    if (spin_26(e, _o_4, _b_20, _b_21, _c_9, _c_10, _v_0) == 0) {
      return 0;
    }
    _v_7 = (u32)_o_4[0];
    _v_8 = _o_4[1];
    o[0] = _b_11;
    o[1] = _b_12;
    o[2] = _b_13;
    o[3] = _v_1;
    o[4] = _v_2;
    o[5] = _v_3;
    o[6] = _v_4;
    o[7] = _v_5;
    o[8] = _v_6;
    o[9] = _v_7;
    o[10] = _v_8;
  break;
  }
  return 1;
}

INLINE Term spin_40(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, u32 r4, Term r5, u32 r6, Term r7, u32 r8, Term r9, u32 r10, Term r11, Term r12, Term r13, Term r14, u32 r15, Term r16, u32 r17, Term r18, u32 r19, Term r20, u32 r21, Term r22) {
  u32 wpoll = 0;
  u32 _v_18 = r0;
  Term _v_19 = r1;
  Term _v_20 = r2;
  Term _v_21 = r3;
  u32 _v_22 = r4;
  Term _v_23 = r5;
  u32 _v_24 = r6;
  Term _v_25 = r7;
  u32 _v_26 = r8;
  Term _v_27 = r9;
  u32 _v_28 = r10;
  Term _v_29 = r11;
  Term _e_11 = r12;
  Term _e_12 = r13;
  Term _e_13 = r14;
  u32 _e_14 = r15;
  Term _e_15 = r16;
  u32 _e_16 = r17;
  Term _e_17 = r18;
  u32 _e_18 = r19;
  Term _e_19 = r20;
  u32 _e_20 = r21;
  Term _e_21 = r22;
  WL_SPIN
    if (_v_18 == 0) {
      o[0] = 1;
      o[1] = _e_11;
      o[2] = _e_12;
      o[3] = _e_13;
      o[4] = _e_14;
      o[5] = _e_15;
      o[6] = _e_16;
      o[7] = _e_17;
      o[8] = _e_18;
      o[9] = _e_19;
      o[10] = _e_20;
      o[11] = _e_21;
    } else {
      o[0] = 1;
      o[1] = _v_19;
      o[2] = _v_20;
      o[3] = _v_21;
      o[4] = _v_22;
      o[5] = _v_23;
      o[6] = _v_24;
      o[7] = _v_25;
      o[8] = _v_26;
      o[9] = _v_27;
      o[10] = _v_28;
      o[11] = _v_29;
    }
  break;
  }
  return 1;
}

INLINE Term spin_41(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _r_0 = r1;
  Term _r_1 = r2;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_8(e, _o_0, _x_0, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_42(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  u32 _m_0 = r1;
  u32 _m_1 = r2;
  Term _m_2 = r3;
  Term _m_3 = r4;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    } else {
      Term _o_0[4];
      if (spin_27(e, _o_0, _n_0, _m_1, _m_2, _m_3) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = (u32)_o_0[1];
      o[2] = _o_0[2];
      o[3] = _o_0[3];
    }
  break;
  }
  return 1;
}

INLINE Term spin_43(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
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

INLINE Term spin_44(Env e, THR Term* o, u32 r0) {
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

INLINE Term spin_45(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  u32 _looped_0 = r1;
  WL_SPIN
    if (_c_0 == 0) {
      if (_looped_0 == 1) {
        o[0] = 1;
      } else {
        o[0] = 0;
      }
    } else if (_c_0 == 1) {
      o[0] = 1;
    } else if (_c_0 == 2) {
      o[0] = 2;
    } else {
      o[0] = 3;
    }
  break;
  }
  return 1;
}

INLINE Term spin_46(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
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

INLINE Term spin_47(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  WL_SPIN
    if (_n_0 == 0) {
      o[0] = 0;
      o[1] = 0;
    } else {
      Term _v_2 = (_n_0 - 1);
      o[0] = 1;
      o[1] = _v_2;
    }
  break;
  }
  return 1;
}

INLINE Term spin_48(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, u32 r5, Term r6, u32 r7, Term r8, u32 r9, Term r10, u32 r11, Term r12) {
  u32 wpoll = 0;
  Term _e_0 = r0;
  Term _e_1 = r1;
  Term _e_2 = r2;
  u32 _e_3 = r3;
  Term _e_4 = r4;
  u32 _e_5 = r5;
  Term _e_6 = r6;
  u32 _e_7 = r7;
  Term _e_8 = r8;
  u32 _e_9 = r9;
  Term _e_10 = r10;
  u32 _m_0 = r11;
  Term _m_1 = r12;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = 0;
      o[1] = 0;
    } else {
      u64 _nd_0 = heap_alloc(e, cls_fit(11));
      e.mem[_nd_0 + 0] = rfc_seal(e, _e_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _e_1);
      e.mem[_nd_0 + 2] = rfc_seal(e, _e_2);
      e.mem[_nd_0 + 3] = rfc_seal(e, _e_3);
      e.mem[_nd_0 + 4] = rfc_seal(e, _e_4);
      e.mem[_nd_0 + 5] = rfc_seal(e, _e_5);
      e.mem[_nd_0 + 6] = rfc_seal(e, _e_6);
      e.mem[_nd_0 + 7] = rfc_seal(e, _e_7);
      e.mem[_nd_0 + 8] = rfc_seal(e, _e_8);
      e.mem[_nd_0 + 9] = rfc_seal(e, _e_9);
      e.mem[_nd_0 + 10] = rfc_seal(e, _e_10);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_catalog_union_Ent, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _m_1);
      o[0] = 1;
      o[1] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_49(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, u32 r5, Term r6, u32 r7, Term r8, u32 r9, Term r10) {
  u32 wpoll = 0;
  Term _e_0 = r0;
  Term _e_1 = r1;
  Term _e_2 = r2;
  u32 _e_3 = r3;
  Term _e_4 = r4;
  u32 _e_5 = r5;
  Term _e_6 = r6;
  u32 _e_7 = r7;
  Term _e_8 = r8;
  u32 _e_9 = r9;
  Term _e_10 = r10;
  WL_SPIN
    o[0] = _e_0;
  break;
  }
  return 1;
}

INLINE Term spin_50(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _t_0 = r0;
  Term _k_0 = r1;
  WL_SPIN
    u32 _v_13 = 0;
    Term _o_1[1];
    if (spin_24(e, _o_1, _k_0) == 0) {
      return 0;
    }
    _v_13 = (u32)_o_1[0];
    u32 _v_14 = 0;
    Term _o_2[1];
    if (spin_25(e, _o_2, _k_0) == 0) {
      return 0;
    }
    _v_14 = (u32)_o_2[0];
    Term _o_3[12];
    if (spin_38(e, _o_3, _t_0, _k_0, _v_13, _v_14) == 0) {
      return 0;
    }
    o[0] = (u32)_o_3[0];
    o[1] = _o_3[1];
    o[2] = _o_3[2];
    o[3] = _o_3[3];
    o[4] = (u32)_o_3[4];
    o[5] = _o_3[5];
    o[6] = (u32)_o_3[6];
    o[7] = _o_3[7];
    o[8] = (u32)_o_3[8];
    o[9] = _o_3[9];
    o[10] = (u32)_o_3[10];
    o[11] = _o_3[11];
  break;
  }
  return 1;
}

INLINE Term spin_51(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, u32 r4, Term r5, u32 r6, Term r7, u32 r8, Term r9, u32 r10, Term r11) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  Term _m_2 = r2;
  Term _m_3 = r3;
  u32 _m_4 = r4;
  Term _m_5 = r5;
  u32 _m_6 = r6;
  Term _m_7 = r7;
  u32 _m_8 = r8;
  Term _m_9 = r9;
  u32 _m_10 = r10;
  Term _m_11 = r11;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = 0;
    } else {
      o[0] = 1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_52(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _cs_1 = r0;
  Term _bt_1 = r1;
  WL_SPIN
    if (term_aux(_cs_1) == CID_Nil) {
      o[0] = 0;
    } else {
      u64 _sp_2 = term_peek(e.mem, _cs_1);
      Term _f_13 = e.mem[_sp_2 + 0];
      Term _f_14 = e.mem[_sp_2 + 1];
      u64 _sp_3 = term_peek(e.mem, _f_13);
      Term _f_15 = e.mem[_sp_3 + 0];
      Term _f_16 = e.mem[_sp_3 + 1];
      Term _f_17 = e.mem[_sp_3 + 2];
      u32 _f_18 = e.mem[_sp_3 + 3];
      Term _f_19 = e.mem[_sp_3 + 4];
      u32 _f_20 = e.mem[_sp_3 + 5];
      Term _f_21 = e.mem[_sp_3 + 6];
      u32 _f_22 = e.mem[_sp_3 + 7];
      Term _f_23 = e.mem[_sp_3 + 8];
      u32 _f_24 = e.mem[_sp_3 + 9];
      Term _f_25 = e.mem[_sp_3 + 10];
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _v_3 = 0;
      Term _v_4 = 0;
      u32 _v_5 = 0;
      Term _v_6 = 0;
      u32 _v_7 = 0;
      Term _v_8 = 0;
      u32 _v_9 = 0;
      Term _v_10 = 0;
      u32 _v_11 = 0;
      Term _v_12 = 0;
      Term _v_13 = 0;
      Term _o_0[1];
      if (spin_49(e, _o_0, _f_15, _f_16, _f_17, _f_18, _f_19, _f_20, _f_21, _f_22, _f_23, _f_24, _f_25) == 0) {
        return 0;
      }
      _v_13 = _o_0[0];
      Term _o_1[12];
      if (spin_50(e, _o_1, _bt_1, _v_13) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      _v_2 = _o_1[1];
      _v_3 = _o_1[2];
      _v_4 = _o_1[3];
      _v_5 = (u32)_o_1[4];
      _v_6 = _o_1[5];
      _v_7 = (u32)_o_1[6];
      _v_8 = _o_1[7];
      _v_9 = (u32)_o_1[8];
      _v_10 = _o_1[9];
      _v_11 = (u32)_o_1[10];
      _v_12 = _o_1[11];
      Term _o_2[1];
      if (spin_51(e, _o_2, _v_1, _v_2, _v_3, _v_4, _v_5, _v_6, _v_7, _v_8, _v_9, _v_10, _v_11, _v_12) == 0) {
        return 0;
      }
      o[0] = (u32)_o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_53(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, u32 r5, Term r6, u32 r7, Term r8, u32 r9, Term r10, u32 r11, Term r12, Term r13, Term r14, u32 r15, Term r16, u32 r17, Term r18, u32 r19, Term r20, u32 r21, Term r22) {
  u32 wpoll = 0;
  Term _b_0 = r0;
  Term _b_1 = r1;
  Term _b_2 = r2;
  u32 _b_3 = r3;
  Term _b_4 = r4;
  u32 _b_5 = r5;
  Term _b_6 = r6;
  u32 _b_7 = r7;
  Term _b_8 = r8;
  u32 _b_9 = r9;
  Term _b_10 = r10;
  u32 _m_0 = r11;
  Term _m_1 = r12;
  Term _m_2 = r13;
  Term _m_3 = r14;
  u32 _m_4 = r15;
  Term _m_5 = r16;
  u32 _m_6 = r17;
  Term _m_7 = r18;
  u32 _m_8 = r19;
  Term _m_9 = r20;
  u32 _m_10 = r21;
  Term _m_11 = r22;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = _b_0;
      o[1] = _b_1;
      o[2] = _b_2;
      o[3] = _b_3;
      o[4] = _b_4;
      o[5] = _b_5;
      o[6] = _b_6;
      o[7] = _b_7;
      o[8] = _b_8;
      o[9] = _b_9;
      o[10] = _b_10;
    } else {
      Term _o_2[11];
      if (spin_39(e, _o_2, _b_0, _b_1, _b_2, _b_3, _b_4, _b_5, _b_6, _b_7, _b_8, _b_9, _b_10, _m_1, _m_2, _m_3, _m_4, _m_5, _m_6, _m_7, _m_8, _m_9, _m_10, _m_11) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
      o[1] = _o_2[1];
      o[2] = _o_2[2];
      o[3] = (u32)_o_2[3];
      o[4] = _o_2[4];
      o[5] = (u32)_o_2[5];
      o[6] = _o_2[6];
      o[7] = (u32)_o_2[7];
      o[8] = _o_2[8];
      o[9] = (u32)_o_2[9];
      o[10] = _o_2[10];
    }
  break;
  }
  return 1;
}

INLINE Term spin_54(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _r_0 = r0;
  Term _r_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_8(e, _o_0, _r_0, _r_1) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_55(Env e, THR Term* o, Term r0, Term r1) {
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

INLINE Term spin_56(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  u32 _m_1 = r1;
  Term _m_2 = r2;
  Term _m_3 = r3;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = 0;
      o[1] = 0;
    } else {
      Term _v_0 = 0;
      Term _o_0[1];
      if (spin_15(e, _o_0, _m_1, _m_2, _m_3) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      o[0] = 1;
      o[1] = _v_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_57(Env e, THR Term* o, u32 r0, Term r1, u32 r2) {
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
      if (spin_44(e, _o_0, _comma_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_58(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
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

INLINE Term spin_59(Env e, THR Term* o, Term r0, u32 r1) {
  u32 wpoll = 0;
  Term _r_4 = r0;
  u32 _r_5 = r1;
  WL_SPIN
    o[0] = _r_4;
  break;
  }
  return 1;
}

INLINE Term spin_60(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  WL_SPIN
    if (_c_0 == 0) {
      o[0] = 0;
    } else if (_c_0 == 1) {
      o[0] = 1ull;
    } else if (_c_0 == 2) {
      o[0] = 2ull;
    } else {
      o[0] = 3ull;
    }
  break;
  }
  return 1;
}

INLINE Term spin_61(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _c_0 = r0;
  WL_SPIN
    if (_c_0 == 0) {
      o[0] = 1;
      o[1] = 0;
    } else if (_c_0 == 1) {
      o[0] = 2;
      o[1] = 0;
    } else {
      Term _n_0 = (_c_0 - 2);
      o[0] = 0;
      o[1] = _n_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_62(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _segs_1 = r0;
  Term _at_0 = r1;
  WL_SPIN
    if (term_aux(_segs_1) == CID_Nil) {
      o[0] = 1;
      o[1] = _at_0;
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _segs_1, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u32 _o_0 = 0;
      Term _o_1 = 0;
      if (term_aux(_f_0) == CID_tools_Name) {
        _o_0 = 0;
        Term _fb_1[1];
        u64 _sp_1 = ctr_take(e, _f_0, 1, _fb_1);
        Term _f_2 = _fb_1[0];
        spare_free(e, cls_fit(1), _sp_1);
        _o_1 = _f_2;
      } else if (term_aux(_f_0) == CID_tools_Up) {
        _o_0 = 1;
      } else {
        _o_0 = 2;
      }
      if (_o_0 == 0) {
        u64 _nd_0 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _o_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _at_0);
        r0 = _f_1;
        r1 = term_ctr(CID_Con, _nd_0);
        _segs_1 = r0;
        _at_0 = r1;
        WL_AGAIN(spin_62);
      } else if (_o_0 == 2) {
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _at_0;
        _segs_1 = r0;
        _at_0 = r1;
        WL_AGAIN(spin_62);
      } else {
        if (term_aux(_at_0) == CID_Nil) {
          term_sink(e, _f_1);
          o[0] = 0;
          o[1] = 0;
          spare_free(e, cls_fit(2), _sp_0);
        } else {
          Term _fb_2[2];
          u64 _sp_2 = ctr_take(e, _at_0, 2, _fb_2);
          Term _f_3 = _fb_2[0];
          Term _f_4 = _fb_2[1];
          spare_free(e, cls_fit(2), _sp_2);
          spare_free(e, cls_fit(2), _sp_0);
          r0 = _f_1;
          r1 = _f_4;
          _segs_1 = r0;
          _at_0 = r1;
          WL_AGAIN(spin_62);
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_63(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _mb_0 = r0;
  Term _mb_1 = r1;
  u32 _mc_0 = r2;
  Term _mc_1 = r3;
  Term _s_0 = r4;
  WL_SPIN
    if (_mb_0 == 1) {
      if (_mc_0 == 1) {
        o[0] = 0;
        o[1] = _mb_1;
        o[2] = _mc_1;
        o[3] = _s_0;
      } else {
        term_sink(e, _mb_1);
        term_sink(e, _s_0);
        o[0] = 1;
        o[1] = 0;
        o[2] = 0;
        o[3] = 0;
      }
    } else {
      if (_mc_0 == 1) {
        term_sink(e, _mc_1);
        term_sink(e, _s_0);
        o[0] = 1;
        o[1] = 0;
        o[2] = 0;
        o[3] = 0;
      } else {
        term_sink(e, _s_0);
        o[0] = 1;
        o[1] = 0;
        o[2] = 0;
        o[3] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_64(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  WL_SPIN
    if (_m_0 == 0) {
      o[0] = 0;
    } else {
      o[0] = nat_chk(e, _m_1 + 1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_65(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _c_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _c_0;
      o[2] = _r_5;
      o[3] = _r_6;
    } else {
      term_sink(e, _c_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_66(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _p_0 = r0;
  Term _p_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    if (_p_0 == 0) {
      Term _v_0 = 0;
      Term _o_0[1];
      if (spin_8(e, _o_0, _p_1, _rest_0) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      Term _o_1[1];
      if (spin_8(e, _o_1, 0, _v_0) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_8(e, _o_2, 1ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_67(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  Term _s_0 = r2;
  WL_SPIN
    if (_m_0 == 1) {
      o[0] = 0;
      o[1] = _m_1;
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

INLINE Term spin_68(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _x_0 = ((u64)(u32)(_r_1));
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_1(e, _o_0, ((u64)_x_0), _r_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[3];
      if (spin_58(e, _o_1, _v_0, _x_0, _r_2) == 0) {
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

INLINE Term spin_69(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _j_0 = r0;
  u32 _j_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_60(e, _o_0, _j_0) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    Term _v_1 = 0;
    Term _o_1[1];
    if (spin_28(e, _o_1, _j_1, _rest_0) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    Term _o_2[1];
    if (spin_8(e, _o_2, _v_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_70(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _segs_0 = r0;
  WL_SPIN
    Term _o_0[2];
    if (spin_62(e, _o_0, _segs_0, term_pak(CID_Nil, 0)) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
    o[1] = _o_0[1];
  break;
  }
  return 1;
}

INLINE Term spin_71(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_1 = r0;
  WL_SPIN
    if (term_aux(_s_1) == CID_SNil) {
      o[0] = 1;
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _s_1, 2, _fb_0);
      u32 _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      term_sink(e, _f_1);
      o[0] = 0;
      spare_free(e, cls_fit(2), _sp_0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_72(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_0 = r0;
  WL_SPIN
    Term _o_0[1];
    if (spin_71(e, _o_0, _s_0) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_73(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
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

INLINE Term spin_74(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _input_1 = r0;
  WL_SPIN
    o[0] = _input_1;
  break;
  }
  return 1;
}

INLINE Term spin_75(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
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

INLINE Term spin_76(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _state_4 = r0;
  u32 _state_5 = r1;
  Term _state_6 = r2;
  Term _state_7 = r3;
  WL_SPIN
    if (_state_4 == 0) {
      term_sink(e, _state_7);
      o[0] = term_pak(CID_Unit, 0);
    } else {
      o[0] = term_pak(CID_Unit, 0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_77(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _a_1 = r0;
  Term _b_1 = r1;
  u32 _c_0 = r2;
  WL_SPIN
    if (term_aux(_a_1) == CID_SNil) {
      if (term_aux(_b_1) == CID_SCon) {
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _b_1, 2, _fb_0);
        u32 _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        term_sink(e, _f_1);
        if (_c_0 == 1) {
          o[0] = 0;
          spare_free(e, cls_fit(2), _sp_0);
        } else {
          o[0] = _c_0;
          spare_free(e, cls_fit(2), _sp_0);
        }
      } else {
        term_sink(e, _b_1);
        o[0] = _c_0;
      }
    } else {
      u64 _sp_1 = term_peek(e.mem, _a_1);
      u32 _f_2 = e.mem[_sp_1 + 0];
      Term _f_3 = e.mem[_sp_1 + 1];
      if (term_aux(_b_1) == CID_SNil) {
        if (_c_0 == 1) {
          o[0] = 2;
        } else {
          o[0] = _c_0;
        }
      } else {
        Term _fb_1[2];
        u64 _sp_2 = ctr_take(e, _b_1, 2, _fb_1);
        u32 _f_4 = _fb_1[0];
        Term _f_5 = _fb_1[1];
        if (_c_0 == 1) {
          spare_free(e, cls_fit(2), _sp_2);
          r0 = _f_3;
          r1 = _f_5;
          r2 = (U32_BIN(_f_2, >, _f_4) + U32_BIN(_f_2, >=, _f_4));
          _a_1 = r0;
          _b_1 = r1;
          _c_0 = r2;
          WL_AGAIN(spin_77);
        } else {
          term_sink(e, _f_5);
          o[0] = _c_0;
          spare_free(e, cls_fit(2), _sp_2);
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_78(Env e, THR Term* o, Term r0) {
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

INLINE Term spin_79(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_1 = r0;
  Term _b_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_77(e, _o_0, _a_1, _b_1, 1) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_80(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_79(e, _o_0, _a_0, _b_0) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_2(e, _o_1, _v_1) == 0) {
      return 0;
    }
    o[0] = (u32)_o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_81(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
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
  WL_CASE(FID_tools_elem)
    Term _xs_0 = r0;
    Term _x_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_0;
        STK(1) = _x_0;
        STK(2) = FID_tools_elem_k6;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_tools_elem_k6, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _x_0;
        WL_CONT = term_tsk(FID_tools_elem_k6, _t_0);
        WL_IDX = 2;
      }
      r0 = _f_1;
      r1 = _x_0;
      _xs_0 = r0;
      _x_0 = r1;
      WL_AGAIN(FID_tools_elem);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tools_elem_k6)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _x_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_1[1];
    if (spin_1(e, _o_1, _f_2, _x_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    r0 = ((_v_0) | (_h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_parent_is)
    Term _real_0 = r0;
    Term _p_0 = r1;
    WL_OPEN
    if (term_aux(_real_0) == CID_Nil) {
      term_sink(e, _p_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _real_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (!DEVICE && !seq && fid_nofk(FID_tools_ids_eq)) {
        u64 _t_0 = task_node(e, FID_tools_ids_eq, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _f_1;
        e.mem[_t_0 + 1] = _p_0;
        return term_tsk(FID_tools_ids_eq, _t_0);
      }
      r0 = _f_1;
      r1 = _p_0;
      WL_JMP(FID_tools_ids_eq);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_cell_sum)
    Term _c_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_c_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _c_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_gateway_width_cell_sum_k9;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_gateway_width_cell_sum_k9, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_gateway_width_cell_sum_k9, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _c_0 = r0;
      WL_AGAIN(FID_gateway_width_cell_sum);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_cell_sum_k9)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _f_2 + _h_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_rules_of)
    Term _xss_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xss_0) == CID_Nil) {
      r0 = 1;
      r1 = term_pak(CID_Nil, 0);
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xss_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_ffi_path_policy_rules_of_k12;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_path_policy_rules_of_k12, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_ffi_path_policy_rules_of_k12, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _xss_0 = r0;
      WL_AGAIN(FID_ffi_path_policy_rules_of);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_rules_of_k12)
    WL_POPN(1);
    Term _f_2 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    u32 _v_1 = 0;
    Term _v_2 = 0;
    Term _o_1[3];
    if (spin_3(e, _o_1, _f_2) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    _v_1 = (u32)_o_1[1];
    _v_2 = _o_1[2];
    Term _o_2[2];
    if (spin_4(e, _o_2, _v_0, _v_1, _v_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = _o_2[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_longer)
    Term _a_0 = r0;
    Term _b_0 = r1;
    WL_OPEN
    _a_0 = term_keep(e, _a_0, 1);
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _a_0;
      STK(1) = _b_0;
      STK(2) = FID_path_policy_longer_k14;
      WL_PUSHN(3);
    } else {
      u64 _t_0 = task_node(e, FID_path_policy_longer_k14, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _a_0;
      e.mem[_t_0 + 1] = _b_0;
      WL_CONT = term_tsk(FID_path_policy_longer_k14, _t_0);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
      u64 _t_1 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _a_0;
      return term_tsk(FID_List_length, _t_1);
    }
    r0 = _a_0;
    WL_JMP(FID_List_length);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_longer_k14)
    WL_POPN(2);
    Term _a_1 = STK(0);
    Term _b_1 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    _b_1 = term_keep(e, _b_1, 1);
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _a_1;
      STK(1) = _b_1;
      STK(2) = _h_0;
      STK(3) = FID_path_policy_longer_k15;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_longer_k15, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _a_1;
      e.mem[_t_2 + 1] = _b_1;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_longer_k15, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
      u64 _t_3 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _b_1;
      return term_tsk(FID_List_length, _t_3);
    }
    r0 = _b_1;
    WL_JMP(FID_List_length);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_longer_k15)
    WL_POPN(3);
    Term _a_2 = STK(0);
    Term _b_2 = STK(1);
    Term _h_2 = STK(2);
    Term _h_1 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_5(e, _o_0, (_h_2 < _h_1), _a_2, _b_2) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_strip)
    Term _real_0 = r0;
    Term _root_0 = r1;
    WL_OPEN
    if (term_aux(_real_0) == CID_Nil) {
      term_sink(e, _root_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _real_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _f_1 = term_keep(e, _f_1, 1);
      u64 _nd_0 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _f_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _f_1);
      _root_0 = term_keep(e, _root_0, 1);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_0;
        STK(1) = _f_1;
        STK(2) = _root_0;
        STK(3) = FID_path_policy_strip_k17;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_path_policy_strip_k17, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _f_1;
        e.mem[_t_0 + 2] = _root_0;
        WL_CONT = term_tsk(FID_path_policy_strip_k17, _t_0);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_tools_ids_eq)) {
        u64 _t_1 = task_node(e, FID_tools_ids_eq, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = term_ctr(CID_Con, _nd_0);
        e.mem[_t_1 + 1] = _root_0;
        return term_tsk(FID_tools_ids_eq, _t_1);
      }
      r0 = term_ctr(CID_Con, _nd_0);
      r1 = _root_0;
      WL_JMP(FID_tools_ids_eq);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_strip_k17)
    WL_POPN(3);
    Term _f_2 = STK(0);
    Term _f_3 = STK(1);
    Term _root_1 = STK(2);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _f_2;
      STK(1) = _h_0;
      STK(2) = FID_path_policy_strip_k18;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_strip_k18, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _f_2;
      e.mem[_t_2 + 1] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_strip_k18, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_strip)) {
      u64 _t_3 = task_node(e, FID_path_policy_strip, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_3;
      e.mem[_t_3 + 1] = _root_1;
      return term_tsk(FID_path_policy_strip, _t_3);
    }
    r0 = _f_3;
    r1 = _root_1;
    WL_JMP(FID_path_policy_strip);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_strip_k18)
    WL_POPN(2);
    Term _f_4 = STK(0);
    u32 _h_2 = STK(1);
    Term _h_1 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_6(e, _o_0, _h_2, _f_4, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_covers)
    u32 _r_0 = r0;
    Term _r_1 = r1;
    Term _real_0 = r2;
    Term _low_0 = r3;
    WL_OPEN
    if (_r_0 == 0) {
      term_sink(e, _low_0);
      if (!DEVICE && !seq && fid_nofk(FID_path_policy_under)) {
        u64 _t_0 = task_node(e, FID_path_policy_under, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _r_1;
        e.mem[_t_0 + 1] = _real_0;
        return term_tsk(FID_path_policy_under, _t_0);
      }
      r0 = _r_1;
      r1 = _real_0;
      WL_JMP(FID_path_policy_under);
    } else if (_r_0 == 1) {
      term_sink(e, _low_0);
      _real_0 = term_keep(e, _real_0, 1);
      _r_1 = term_keep(e, _r_1, 1);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _r_1;
        STK(1) = _real_0;
        STK(2) = FID_path_policy_covers_k20;
        WL_PUSHN(3);
      } else {
        u64 _t_1 = task_node(e, FID_path_policy_covers_k20, WL_CONT, WL_IDX, 1);
        e.mem[_t_1 + 0] = _r_1;
        e.mem[_t_1 + 1] = _real_0;
        WL_CONT = term_tsk(FID_path_policy_covers_k20, _t_1);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_tools_ids_eq)) {
        u64 _t_2 = task_node(e, FID_tools_ids_eq, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = _real_0;
        e.mem[_t_2 + 1] = _r_1;
        return term_tsk(FID_tools_ids_eq, _t_2);
      }
      r0 = _real_0;
      r1 = _r_1;
      WL_JMP(FID_tools_ids_eq);
    } else {
      term_sink(e, _real_0);
      if (!DEVICE && !seq && fid_nofk(FID_tools_elem)) {
        u64 _t_5 = task_node(e, FID_tools_elem, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _low_0;
        e.mem[_t_5 + 1] = _r_1;
        return term_tsk(FID_tools_elem, _t_5);
      }
      r0 = _low_0;
      r1 = _r_1;
      WL_JMP(FID_tools_elem);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_covers_k20)
    WL_POPN(2);
    Term _r_2 = STK(0);
    Term _real_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_path_policy_covers_k21;
      WL_PUSHN(2);
    } else {
      u64 _t_3 = task_node(e, FID_path_policy_covers_k21, WL_CONT, WL_IDX, 1);
      e.mem[_t_3 + 0] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_covers_k21, _t_3);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_parent_is)) {
      u64 _t_4 = task_node(e, FID_path_policy_parent_is, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _real_1;
      e.mem[_t_4 + 1] = _r_2;
      return term_tsk(FID_path_policy_parent_is, _t_4);
    }
    r0 = _real_1;
    r1 = _r_2;
    WL_JMP(FID_path_policy_parent_is);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_covers_k21)
    WL_POPN(1);
    u32 _h_2 = STK(0);
    u32 _h_1 = r0;
    WL_OPEN
    r0 = ((_h_2) | (_h_1));
    WL_RETN(1);
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
        STK(1) = FID_wire_put_str_go_k25;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_str_go_k25, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_put_str_go_k25, _t_0);
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
  WL_CASE(FID_wire_put_str_go_k25)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_7(e, _o_0, _f_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    r1 = _o_0[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_rules)
    u32 _m_0 = r0;
    Term _m_1 = r1;
    WL_OPEN
    if (_m_0 == 0) {
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    } else {
      if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_rules_of)) {
        u64 _t_0 = task_node(e, FID_ffi_path_policy_rules_of, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _m_1;
        return term_tsk(FID_ffi_path_policy_rules_of, _t_0);
      }
      r0 = _m_1;
      WL_JMP(FID_ffi_path_policy_rules_of);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_entries)
    Term _rs_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_rs_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u32 _o_0 = 0;
      Term _o_1 = 0;
      if (term_aux(_f_0) == CID_path_policy_Tree) {
        _o_0 = 0;
        Term _fb_1[1];
        u64 _sp_1 = ctr_take(e, _f_0, 1, _fb_1);
        Term _f_2 = _fb_1[0];
        spare_free(e, cls_fit(1), _sp_1);
        _o_1 = _f_2;
      } else if (term_aux(_f_0) == CID_path_policy_Dir) {
        _o_0 = 1;
        Term _fb_2[1];
        u64 _sp_2 = ctr_take(e, _f_0, 1, _fb_2);
        Term _f_3 = _fb_2[0];
        spare_free(e, cls_fit(1), _sp_2);
        _o_1 = _f_3;
      } else {
        _o_0 = 2;
        Term _fb_3[1];
        u64 _sp_3 = ctr_take(e, _f_0, 1, _fb_3);
        Term _f_4 = _fb_3[0];
        spare_free(e, cls_fit(1), _sp_3);
        _o_1 = _f_4;
      }
      if (_o_0 == 0) {
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _o_1;
          STK(1) = FID_path_policy_entries_k32;
          WL_PUSHN(2);
        } else {
          u64 _t_0 = task_node(e, FID_path_policy_entries_k32, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _o_1;
          WL_CONT = term_tsk(FID_path_policy_entries_k32, _t_0);
          WL_IDX = 1;
        }
        r0 = _f_1;
        _rs_0 = r0;
        WL_AGAIN(FID_path_policy_entries);
      } else if (_o_0 == 1) {
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _o_1;
          STK(1) = FID_path_policy_entries_k33;
          WL_PUSHN(2);
        } else {
          u64 _t_1 = task_node(e, FID_path_policy_entries_k33, WL_CONT, WL_IDX, 1);
          e.mem[_t_1 + 0] = _o_1;
          WL_CONT = term_tsk(FID_path_policy_entries_k33, _t_1);
          WL_IDX = 1;
        }
        r0 = _f_1;
        _rs_0 = r0;
        WL_AGAIN(FID_path_policy_entries);
      } else {
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        _rs_0 = r0;
        WL_AGAIN(FID_path_policy_entries);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_entries_k32)
    WL_POPN(1);
    Term _o_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _o_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_entries_k33)
    WL_POPN(1);
    Term _o_3 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _o_3);
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_1);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_below)
    Term _real_0 = r0;
    u32 _root_0 = r1;
    Term _root_1 = r2;
    WL_OPEN
    if (_root_0 == 0) {
      r0 = _real_0;
      WL_RETN(1);
    } else {
      if (!DEVICE && !seq && fid_nofk(FID_path_policy_strip)) {
        u64 _t_0 = task_node(e, FID_path_policy_strip, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _real_0;
        e.mem[_t_0 + 1] = _root_1;
        return term_tsk(FID_path_policy_strip, _t_0);
      }
      r0 = _real_0;
      r1 = _root_1;
      WL_JMP(FID_path_policy_strip);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_covers)
    Term _rs_0 = r0;
    Term _real_0 = r1;
    Term _low_0 = r2;
    WL_OPEN
    if (term_aux(_rs_0) == CID_Nil) {
      term_sink(e, _real_0);
      term_sink(e, _low_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      u32 _o_0 = 0;
      Term _o_1 = 0;
      if (term_aux(_f_0) == CID_path_policy_Tree) {
        _o_0 = 0;
        Term _fb_1[1];
        u64 _sp_1 = ctr_take(e, _f_0, 1, _fb_1);
        Term _f_2 = _fb_1[0];
        spare_free(e, cls_fit(1), _sp_1);
        _o_1 = _f_2;
      } else if (term_aux(_f_0) == CID_path_policy_Dir) {
        _o_0 = 1;
        Term _fb_2[1];
        u64 _sp_2 = ctr_take(e, _f_0, 1, _fb_2);
        Term _f_3 = _fb_2[0];
        spare_free(e, cls_fit(1), _sp_2);
        _o_1 = _f_3;
      } else {
        _o_0 = 2;
        Term _fb_3[1];
        u64 _sp_3 = ctr_take(e, _f_0, 1, _fb_3);
        Term _f_4 = _fb_3[0];
        spare_free(e, cls_fit(1), _sp_3);
        _o_1 = _f_4;
      }
      _real_0 = term_keep(e, _real_0, 1);
      _low_0 = term_keep(e, _low_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_1;
        STK(1) = _real_0;
        STK(2) = _low_0;
        STK(3) = FID_path_policy_any_covers_k37;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_path_policy_any_covers_k37, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        e.mem[_t_0 + 1] = _real_0;
        e.mem[_t_0 + 2] = _low_0;
        WL_CONT = term_tsk(FID_path_policy_any_covers_k37, _t_0);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_path_policy_covers)) {
        u64 _t_1 = task_node(e, FID_path_policy_covers, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _o_0;
        e.mem[_t_1 + 1] = _o_1;
        e.mem[_t_1 + 2] = _real_0;
        e.mem[_t_1 + 3] = _low_0;
        return term_tsk(FID_path_policy_covers, _t_1);
      }
      r0 = _o_0;
      r1 = _o_1;
      r2 = _real_0;
      r3 = _low_0;
      WL_JMP(FID_path_policy_covers);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_covers_k37)
    WL_POPN(3);
    Term _f_5 = STK(0);
    Term _real_1 = STK(1);
    Term _low_1 = STK(2);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_path_policy_any_covers_k38;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_any_covers_k38, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_any_covers_k38, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_covers)) {
      u64 _t_3 = task_node(e, FID_path_policy_any_covers, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_5;
      e.mem[_t_3 + 1] = _real_1;
      e.mem[_t_3 + 2] = _low_1;
      return term_tsk(FID_path_policy_any_covers, _t_3);
    }
    r0 = _f_5;
    r1 = _real_1;
    r2 = _low_1;
    WL_JMP(FID_path_policy_any_covers);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_covers_k38)
    WL_POPN(1);
    u32 _h_2 = STK(0);
    u32 _h_1 = r0;
    WL_OPEN
    r0 = ((_h_2) | (_h_1));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_at)
    Term _rest_0 = r0;
    Term _w_0 = r1;
    Term _row_0 = r2;
    Term _i_0 = r3;
    WL_OPEN
    if (term_aux(_rest_0) == CID_Nil) {
      term_sink(e, _row_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rest_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _row_0 = term_keep(e, _row_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _f_0;
        STK(1) = _f_1;
        STK(2) = _w_0;
        STK(3) = _row_0;
        STK(4) = _i_0;
        STK(5) = FID_gateway_width_pads_at_k42;
        WL_PUSHN(6);
      } else {
        u64 _t_0 = task_node(e, FID_gateway_width_pads_at_k42, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _f_1;
        e.mem[_t_0 + 2] = _w_0;
        e.mem[_t_0 + 3] = _row_0;
        e.mem[_t_0 + 4] = _i_0;
        WL_CONT = term_tsk(FID_gateway_width_pads_at_k42, _t_0);
        WL_IDX = 5;
      }
      if (!DEVICE && !seq && fid_nofk(FID_gateway_width_get_w)) {
        u64 _t_1 = task_node(e, FID_gateway_width_get_w, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _row_0;
        e.mem[_t_1 + 1] = 0;
        e.mem[_t_1 + 2] = _i_0;
        return term_tsk(FID_gateway_width_get_w, _t_1);
      }
      r0 = _row_0;
      r1 = 0;
      r2 = _i_0;
      WL_JMP(FID_gateway_width_get_w);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_at_k42)
    WL_POPN(5);
    Term _f_2 = STK(0);
    Term _f_3 = STK(1);
    Term _w_1 = STK(2);
    Term _row_1 = STK(3);
    Term _i_1 = STK(4);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _w_1;
      STK(1) = _h_0;
      STK(2) = FID_gateway_width_pads_at_k43;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_gateway_width_pads_at_k43, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _w_1;
      e.mem[_t_2 + 1] = _h_0;
      WL_CONT = term_tsk(FID_gateway_width_pads_at_k43, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_pads_at)) {
      u64 _t_3 = task_node(e, FID_gateway_width_pads_at, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_3;
      e.mem[_t_3 + 1] = _f_2;
      e.mem[_t_3 + 2] = _row_1;
      e.mem[_t_3 + 3] = nat_chk(e, _i_1 + 1);
      return term_tsk(FID_gateway_width_pads_at, _t_3);
    }
    r0 = _f_3;
    r1 = _f_2;
    r2 = _row_1;
    r3 = nat_chk(e, _i_1 + 1);
    WL_JMP(FID_gateway_width_pads_at);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_at_k43)
    WL_POPN(2);
    Term _w_2 = STK(0);
    Term _h_2 = STK(1);
    Term _h_1 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, (_w_2 < _h_2 ? 0 : _w_2 - _h_2));
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_1);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_get_w)
    Term _row_0 = r0;
    u32 _m_0 = r1;
    Term _i_0 = r2;
    WL_OPEN
    WL_SPIN
    if (term_aux(_row_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _row_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      if (_i_0 == 0) {
        term_sink(e, _f_1);
        if (_m_0 == 0) {
          spare_free(e, cls_fit(2), _sp_0);
          if (!DEVICE && !seq && fid_nofk(FID_gateway_width_cell_sum)) {
            u64 _t_0 = task_node(e, FID_gateway_width_cell_sum, WL_CONT, WL_IDX, 0);
            e.mem[_t_0 + 0] = _f_0;
            return term_tsk(FID_gateway_width_cell_sum, _t_0);
          }
          r0 = _f_0;
          WL_JMP(FID_gateway_width_cell_sum);
        } else {
          spare_free(e, cls_fit(2), _sp_0);
          if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
            u64 _t_1 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
            e.mem[_t_1 + 0] = _f_0;
            return term_tsk(FID_List_length, _t_1);
          }
          r0 = _f_0;
          WL_JMP(FID_List_length);
        }
      } else {
        term_sink(e, _f_0);
        Term _p_0 = (_i_0 - 1);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _m_0;
        r2 = _p_0;
        _row_0 = r0;
        _m_0 = r1;
        _i_0 = r2;
        WL_AGAIN(FID_gateway_width_get_w);
      }
    }
    WL_SPUN
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
          STK(1) = FID_wire_take_k46;
          WL_PUSHN(2);
        } else {
          u64 _t_0 = task_node(e, FID_wire_take_k46, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_0;
          WL_CONT = term_tsk(FID_wire_take_k46, _t_0);
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
  WL_CASE(FID_wire_take_k46)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_16(e, _o_0, _f_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_str)
    Term _a_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_str_k48;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_str_k48, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_str_k48, _t_0);
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
  WL_CASE(FID_wire_put_str_k48)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[1];
    if (spin_17(e, _o_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tools_ids_eq)
    Term _xs_0 = r0;
    Term _ys_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      if (term_aux(_ys_0) == CID_Nil) {
        r0 = 1;
        WL_RETN(1);
      } else {
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _ys_0, 2, _fb_0);
        Term _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        term_sink(e, _f_1);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 0;
        WL_RETN(1);
      }
    } else {
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _xs_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      if (term_aux(_ys_0) == CID_Nil) {
        term_sink(e, _f_3);
        spare_free(e, cls_fit(2), _sp_1);
        r0 = 0;
        WL_RETN(1);
      } else {
        Term _fb_2[2];
        u64 _sp_2 = ctr_take(e, _ys_0, 2, _fb_2);
        Term _f_4 = _fb_2[0];
        Term _f_5 = _fb_2[1];
        spare_free(e, cls_fit(2), _sp_2);
        spare_free(e, cls_fit(2), _sp_1);
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _f_2;
          STK(1) = _f_4;
          STK(2) = FID_tools_ids_eq_k56;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_tools_ids_eq_k56, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_2;
          e.mem[_t_0 + 1] = _f_4;
          WL_CONT = term_tsk(FID_tools_ids_eq_k56, _t_0);
          WL_IDX = 2;
        }
        r0 = _f_3;
        r1 = _f_5;
        _xs_0 = r0;
        _ys_0 = r1;
        WL_AGAIN(FID_tools_ids_eq);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tools_ids_eq_k56)
    WL_POPN(2);
    Term _f_6 = STK(0);
    Term _f_7 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_1(e, _o_0, _f_6, _f_7) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_19(e, _o_1, _v_0, _h_0) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_under)
    Term _p_0 = r0;
    Term _real_0 = r1;
    WL_OPEN
    if (term_aux(_real_0) == CID_Nil) {
      if (!DEVICE && !seq && fid_nofk(FID_tools_ids_eq)) {
        u64 _t_0 = task_node(e, FID_tools_ids_eq, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _p_0;
        e.mem[_t_0 + 1] = term_pak(CID_Nil, 0);
        return term_tsk(FID_tools_ids_eq, _t_0);
      }
      r0 = _p_0;
      r1 = term_pak(CID_Nil, 0);
      WL_JMP(FID_tools_ids_eq);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _real_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _f_1 = term_keep(e, _f_1, 1);
      u64 _nd_0 = _sp_0 >= HEAP_OFF ? _sp_0 : heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, _f_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _f_1);
      _p_0 = term_keep(e, _p_0, 1);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _p_0;
        STK(1) = _f_1;
        STK(2) = FID_path_policy_under_k60;
        WL_PUSHN(3);
      } else {
        u64 _t_1 = task_node(e, FID_path_policy_under_k60, WL_CONT, WL_IDX, 1);
        e.mem[_t_1 + 0] = _p_0;
        e.mem[_t_1 + 1] = _f_1;
        WL_CONT = term_tsk(FID_path_policy_under_k60, _t_1);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_tools_ids_eq)) {
        u64 _t_2 = task_node(e, FID_tools_ids_eq, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = _p_0;
        e.mem[_t_2 + 1] = term_ctr(CID_Con, _nd_0);
        return term_tsk(FID_tools_ids_eq, _t_2);
      }
      r0 = _p_0;
      r1 = term_ctr(CID_Con, _nd_0);
      WL_JMP(FID_tools_ids_eq);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_under_k60)
    WL_POPN(2);
    Term _p_1 = STK(0);
    Term _f_2 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_path_policy_under_k61;
      WL_PUSHN(2);
    } else {
      u64 _t_3 = task_node(e, FID_path_policy_under_k61, WL_CONT, WL_IDX, 1);
      e.mem[_t_3 + 0] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_under_k61, _t_3);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_under)) {
      u64 _t_4 = task_node(e, FID_path_policy_under, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _p_1;
      e.mem[_t_4 + 1] = _f_2;
      return term_tsk(FID_path_policy_under, _t_4);
    }
    r0 = _p_1;
    r1 = _f_2;
    WL_JMP(FID_path_policy_under);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_under_k61)
    WL_POPN(1);
    u32 _h_2 = STK(0);
    u32 _h_1 = r0;
    WL_OPEN
    r0 = ((_h_2) | (_h_1));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_root_of)
    Term _rs_0 = r0;
    Term _real_0 = r1;
    WL_OPEN
    if (term_aux(_rs_0) == CID_Nil) {
      term_sink(e, _real_0);
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _f_0 = term_keep(e, _f_0, 1);
      _real_0 = term_keep(e, _real_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_0;
        STK(1) = _f_1;
        STK(2) = _real_0;
        STK(3) = FID_path_policy_root_of_k64;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_path_policy_root_of_k64, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _f_1;
        e.mem[_t_0 + 2] = _real_0;
        WL_CONT = term_tsk(FID_path_policy_root_of_k64, _t_0);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_path_policy_under)) {
        u64 _t_1 = task_node(e, FID_path_policy_under, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _f_0;
        e.mem[_t_1 + 1] = _real_0;
        return term_tsk(FID_path_policy_under, _t_1);
      }
      r0 = _f_0;
      r1 = _real_0;
      WL_JMP(FID_path_policy_under);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_root_of_k64)
    WL_POPN(3);
    Term _f_2 = STK(0);
    Term _f_3 = STK(1);
    Term _real_1 = STK(2);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _f_2;
      STK(1) = _h_0;
      STK(2) = FID_path_policy_root_of_k65;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_root_of_k65, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _f_2;
      e.mem[_t_2 + 1] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_root_of_k65, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_root_of)) {
      u64 _t_3 = task_node(e, FID_path_policy_root_of, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_3;
      e.mem[_t_3 + 1] = _real_1;
      return term_tsk(FID_path_policy_root_of, _t_3);
    }
    r0 = _f_3;
    r1 = _real_1;
    WL_JMP(FID_path_policy_root_of);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_root_of_k65)
    WL_POPN(2);
    Term _f_4 = STK(0);
    u32 _h_3 = STK(1);
    u32 _h_1 = r0;
    Term _h_2 = r1;
    WL_OPEN
    if (_h_3 == 0) {
      term_sink(e, _f_4);
      r0 = _h_1;
      r1 = _h_2;
      WL_RETN(2);
    } else {
      if (_h_1 == 0) {
        r0 = 1;
        r1 = _f_4;
        WL_RETN(2);
      } else {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_path_policy_root_of_k66;
          WL_PUSHN(1);
        } else {
          u64 _t_4 = task_node(e, FID_path_policy_root_of_k66, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_path_policy_root_of_k66, _t_4);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_path_policy_longer)) {
          u64 _t_5 = task_node(e, FID_path_policy_longer, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _f_4;
          e.mem[_t_5 + 1] = _h_2;
          return term_tsk(FID_path_policy_longer, _t_5);
        }
        r0 = _f_4;
        r1 = _h_2;
        WL_JMP(FID_path_policy_longer);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_root_of_k66)
    Term _h_4 = r0;
    WL_OPEN
    r0 = 1;
    r1 = _h_4;
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects)
    Term _pol_0 = r0;
    Term _pol_1 = r1;
    Term _pol_2 = r2;
    Term _real_0 = r3;
    WL_OPEN
    Term _v_0 = 0;
    _pol_0 = term_keep(e, _pol_0, 1);
    _pol_1 = term_keep(e, _pol_1, 1);
    _pol_2 = term_keep(e, _pol_2, 1);
    Term _o_0[1];
    if (spin_20(e, _o_0, _pol_0, _pol_1, _pol_2) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    _real_0 = term_keep(e, _real_0, 1);
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _pol_0;
      STK(1) = _pol_1;
      STK(2) = _pol_2;
      STK(3) = _real_0;
      STK(4) = FID_path_policy_protects_k68;
      WL_PUSHN(5);
    } else {
      u64 _t_0 = task_node(e, FID_path_policy_protects_k68, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _pol_0;
      e.mem[_t_0 + 1] = _pol_1;
      e.mem[_t_0 + 2] = _pol_2;
      e.mem[_t_0 + 3] = _real_0;
      WL_CONT = term_tsk(FID_path_policy_protects_k68, _t_0);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_root_of)) {
      u64 _t_1 = task_node(e, FID_path_policy_root_of, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _v_0;
      e.mem[_t_1 + 1] = _real_0;
      return term_tsk(FID_path_policy_root_of, _t_1);
    }
    r0 = _v_0;
    r1 = _real_0;
    WL_JMP(FID_path_policy_root_of);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects_k68)
    WL_POPN(4);
    Term _pol_3 = STK(0);
    Term _pol_4 = STK(1);
    Term _pol_5 = STK(2);
    Term _real_1 = STK(3);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    _real_1 = term_keep(e, _real_1, 1);
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _pol_3;
      STK(1) = _pol_4;
      STK(2) = _pol_5;
      STK(3) = _real_1;
      STK(4) = FID_path_policy_protects_k69;
      WL_PUSHN(5);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_protects_k69, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _pol_3;
      e.mem[_t_2 + 1] = _pol_4;
      e.mem[_t_2 + 2] = _pol_5;
      e.mem[_t_2 + 3] = _real_1;
      WL_CONT = term_tsk(FID_path_policy_protects_k69, _t_2);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_below)) {
      u64 _t_3 = task_node(e, FID_path_policy_below, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _real_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      return term_tsk(FID_path_policy_below, _t_3);
    }
    r0 = _real_1;
    r1 = _h_0;
    r2 = _h_1;
    WL_JMP(FID_path_policy_below);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects_k69)
    WL_POPN(4);
    Term _pol_6 = STK(0);
    Term _pol_7 = STK(1);
    Term _pol_8 = STK(2);
    Term _real_2 = STK(3);
    Term _h_2 = r0;
    WL_OPEN
    Term _v_1 = 0;
    _pol_6 = term_keep(e, _pol_6, 1);
    _pol_7 = term_keep(e, _pol_7, 1);
    _pol_8 = term_keep(e, _pol_8, 1);
    Term _o_1[1];
    if (spin_21(e, _o_1, _pol_6, _pol_7, _pol_8) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    _real_2 = term_keep(e, _real_2, 1);
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _pol_6;
      STK(1) = _pol_7;
      STK(2) = _pol_8;
      STK(3) = _real_2;
      STK(4) = FID_path_policy_protects_k70;
      WL_PUSHN(5);
    } else {
      u64 _t_4 = task_node(e, FID_path_policy_protects_k70, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _pol_6;
      e.mem[_t_4 + 1] = _pol_7;
      e.mem[_t_4 + 2] = _pol_8;
      e.mem[_t_4 + 3] = _real_2;
      WL_CONT = term_tsk(FID_path_policy_protects_k70, _t_4);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_covers)) {
      u64 _t_5 = task_node(e, FID_path_policy_any_covers, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _v_1;
      e.mem[_t_5 + 1] = _real_2;
      e.mem[_t_5 + 2] = _h_2;
      return term_tsk(FID_path_policy_any_covers, _t_5);
    }
    r0 = _v_1;
    r1 = _real_2;
    r2 = _h_2;
    WL_JMP(FID_path_policy_any_covers);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects_k70)
    WL_POPN(4);
    Term _pol_9 = STK(0);
    Term _pol_10 = STK(1);
    Term _pol_11 = STK(2);
    Term _real_3 = STK(3);
    u32 _h_3 = r0;
    WL_OPEN
    Term _v_2 = 0;
    _pol_9 = term_keep(e, _pol_9, 1);
    _pol_10 = term_keep(e, _pol_10, 1);
    _pol_11 = term_keep(e, _pol_11, 1);
    Term _o_2[1];
    if (spin_21(e, _o_2, _pol_9, _pol_10, _pol_11) == 0) {
      return 0;
    }
    _v_2 = _o_2[0];
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _pol_9;
      STK(1) = _pol_10;
      STK(2) = _pol_11;
      STK(3) = _real_3;
      STK(4) = _h_3;
      STK(5) = FID_path_policy_protects_k71;
      WL_PUSHN(6);
    } else {
      u64 _t_6 = task_node(e, FID_path_policy_protects_k71, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _pol_9;
      e.mem[_t_6 + 1] = _pol_10;
      e.mem[_t_6 + 2] = _pol_11;
      e.mem[_t_6 + 3] = _real_3;
      e.mem[_t_6 + 4] = _h_3;
      WL_CONT = term_tsk(FID_path_policy_protects_k71, _t_6);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_entries)) {
      u64 _t_7 = task_node(e, FID_path_policy_entries, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _v_2;
      return term_tsk(FID_path_policy_entries, _t_7);
    }
    r0 = _v_2;
    WL_JMP(FID_path_policy_entries);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects_k71)
    WL_POPN(5);
    Term _pol_12 = STK(0);
    Term _pol_13 = STK(1);
    Term _pol_14 = STK(2);
    Term _real_4 = STK(3);
    u32 _h_5 = STK(4);
    Term _h_4 = r0;
    WL_OPEN
    Term _v_3 = 0;
    Term _o_3[1];
    if (spin_22(e, _o_3, _pol_12, _pol_13, _pol_14) == 0) {
      return 0;
    }
    _v_3 = _o_3[0];
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _real_4;
      STK(1) = _h_5;
      STK(2) = FID_path_policy_protects_k72;
      WL_PUSHN(3);
    } else {
      u64 _t_8 = task_node(e, FID_path_policy_protects_k72, WL_CONT, WL_IDX, 1);
      e.mem[_t_8 + 0] = _real_4;
      e.mem[_t_8 + 1] = _h_5;
      WL_CONT = term_tsk(FID_path_policy_protects_k72, _t_8);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_append)) {
      u64 _t_9 = task_node(e, FID_List_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_9 + 0] = _h_4;
      e.mem[_t_9 + 1] = _v_3;
      return term_tsk(FID_List_append, _t_9);
    }
    r0 = _h_4;
    r1 = _v_3;
    WL_JMP(FID_List_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects_k72)
    WL_POPN(2);
    Term _real_5 = STK(0);
    u32 _h_7 = STK(1);
    Term _h_6 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_7;
      STK(1) = FID_path_policy_protects_k73;
      WL_PUSHN(2);
    } else {
      u64 _t_10 = task_node(e, FID_path_policy_protects_k73, WL_CONT, WL_IDX, 1);
      e.mem[_t_10 + 0] = _h_7;
      WL_CONT = term_tsk(FID_path_policy_protects_k73, _t_10);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_ancestor)) {
      u64 _t_11 = task_node(e, FID_path_policy_any_ancestor, WL_CONT, WL_IDX, 0);
      e.mem[_t_11 + 0] = _h_6;
      e.mem[_t_11 + 1] = _real_5;
      return term_tsk(FID_path_policy_any_ancestor, _t_11);
    }
    r0 = _h_6;
    r1 = _real_5;
    WL_JMP(FID_path_policy_any_ancestor);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_protects_k73)
    WL_POPN(1);
    u32 _h_9 = STK(0);
    u32 _h_8 = r0;
    WL_OPEN
    r0 = ((_h_9) | (_h_8));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tiny_elem)
    Term _xs_0 = r0;
    Term _x_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_0;
        STK(1) = _x_0;
        STK(2) = FID_tiny_elem_k83;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_tiny_elem_k83, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _x_0;
        WL_CONT = term_tsk(FID_tiny_elem_k83, _t_0);
        WL_IDX = 2;
      }
      r0 = _f_1;
      r1 = _x_0;
      _xs_0 = r0;
      _x_0 = r1;
      WL_AGAIN(FID_tiny_elem);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tiny_elem_k83)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _x_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_1(e, _o_0, _f_2, _x_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    r0 = ((_v_0) | (_h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_row)
    Term _ws_0 = r0;
    Term _row_0 = r1;
    WL_OPEN
    if (term_aux(_ws_0) == CID_Nil) {
      term_sink(e, _row_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ws_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (!DEVICE && !seq && fid_nofk(FID_gateway_width_pads_at)) {
        u64 _t_0 = task_node(e, FID_gateway_width_pads_at, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _f_1;
        e.mem[_t_0 + 1] = _f_0;
        e.mem[_t_0 + 2] = _row_0;
        e.mem[_t_0 + 3] = 0;
        return term_tsk(FID_gateway_width_pads_at, _t_0);
      }
      r0 = _f_1;
      r1 = _f_0;
      r2 = _row_0;
      r3 = 0;
      WL_JMP(FID_gateway_width_pads_at);
    }
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
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      term_sink(e, _f_0);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_List_length_k88;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_List_length_k88, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_List_length_k88, _t_0);
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
  WL_CASE(FID_List_length_k88)
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _h_0 + 1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_col_w)
    Term _rows_0 = r0;
    u32 _m_0 = r1;
    Term _i_0 = r2;
    WL_OPEN
    if (term_aux(_rows_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rows_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_1;
        STK(1) = _m_0;
        STK(2) = _i_0;
        STK(3) = FID_gateway_width_col_w_k90;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_gateway_width_col_w_k90, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        e.mem[_t_0 + 1] = _m_0;
        e.mem[_t_0 + 2] = _i_0;
        WL_CONT = term_tsk(FID_gateway_width_col_w_k90, _t_0);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_gateway_width_get_w)) {
        u64 _t_1 = task_node(e, FID_gateway_width_get_w, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _f_0;
        e.mem[_t_1 + 1] = _m_0;
        e.mem[_t_1 + 2] = _i_0;
        return term_tsk(FID_gateway_width_get_w, _t_1);
      }
      r0 = _f_0;
      r1 = _m_0;
      r2 = _i_0;
      WL_JMP(FID_gateway_width_get_w);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_col_w_k90)
    WL_POPN(3);
    Term _f_2 = STK(0);
    u32 _m_1 = STK(1);
    Term _i_1 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_gateway_width_col_w_k91;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_gateway_width_col_w_k91, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_gateway_width_col_w_k91, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_col_w)) {
      u64 _t_3 = task_node(e, FID_gateway_width_col_w, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_2;
      e.mem[_t_3 + 1] = _m_1;
      e.mem[_t_3 + 2] = _i_1;
      return term_tsk(FID_gateway_width_col_w, _t_3);
    }
    r0 = _f_2;
    r1 = _m_1;
    r2 = _i_1;
    WL_JMP(FID_gateway_width_col_w);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_col_w_k91)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    r0 = (_h_2 > _h_1 ? _h_2 : _h_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_one)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, 0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _rest_0);
      r0 = term_ctr(CID_Con, _nd_0);
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
        STK(1) = FID_wire_flat_one_k93;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_flat_one_k93, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_flat_one_k93, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_flat_one);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_one_k93)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, nat_chk(e, _f_2 + 1));
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
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
        STK(1) = FID_wire_value_k97;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_value_k97, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_value_k97, _t_0);
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
  WL_CASE(FID_wire_value_k97)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _f_2 + nat_mul(e, 10ull, _h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_ancestor)
    Term _ps_0 = r0;
    Term _real_0 = r1;
    WL_OPEN
    if (term_aux(_ps_0) == CID_Nil) {
      term_sink(e, _real_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ps_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _real_0 = term_keep(e, _real_0, 1);
      _f_0 = term_keep(e, _f_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_0;
        STK(1) = _f_1;
        STK(2) = _real_0;
        STK(3) = FID_path_policy_any_ancestor_k109;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_path_policy_any_ancestor_k109, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _f_1;
        e.mem[_t_0 + 2] = _real_0;
        WL_CONT = term_tsk(FID_path_policy_any_ancestor_k109, _t_0);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_path_policy_under)) {
        u64 _t_1 = task_node(e, FID_path_policy_under, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _real_0;
        e.mem[_t_1 + 1] = _f_0;
        return term_tsk(FID_path_policy_under, _t_1);
      }
      r0 = _real_0;
      r1 = _f_0;
      WL_JMP(FID_path_policy_under);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_ancestor_k109)
    WL_POPN(3);
    Term _f_2 = STK(0);
    Term _f_3 = STK(1);
    Term _real_1 = STK(2);
    u32 _h_0 = r0;
    WL_OPEN
    _real_1 = term_keep(e, _real_1, 1);
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _f_3;
      STK(1) = _real_1;
      STK(2) = _h_0;
      STK(3) = FID_path_policy_any_ancestor_k110;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_any_ancestor_k110, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _f_3;
      e.mem[_t_2 + 1] = _real_1;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_any_ancestor_k110, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_tools_ids_eq)) {
      u64 _t_3 = task_node(e, FID_tools_ids_eq, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _real_1;
      e.mem[_t_3 + 1] = _f_2;
      return term_tsk(FID_tools_ids_eq, _t_3);
    }
    r0 = _real_1;
    r1 = _f_2;
    WL_JMP(FID_tools_ids_eq);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_ancestor_k110)
    WL_POPN(3);
    Term _f_4 = STK(0);
    Term _real_2 = STK(1);
    u32 _h_2 = STK(2);
    u32 _h_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _h_2;
      STK(1) = _h_1;
      STK(2) = FID_path_policy_any_ancestor_k111;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_path_policy_any_ancestor_k111, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _h_2;
      e.mem[_t_4 + 1] = _h_1;
      WL_CONT = term_tsk(FID_path_policy_any_ancestor_k111, _t_4);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_ancestor)) {
      u64 _t_5 = task_node(e, FID_path_policy_any_ancestor, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _f_4;
      e.mem[_t_5 + 1] = _real_2;
      return term_tsk(FID_path_policy_any_ancestor, _t_5);
    }
    r0 = _f_4;
    r1 = _real_2;
    WL_JMP(FID_path_policy_any_ancestor);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_ancestor_k111)
    WL_POPN(2);
    u32 _h_4 = STK(0);
    u32 _h_5 = STK(1);
    u32 _h_3 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_35(e, _o_0, _h_5) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_19(e, _o_1, _h_4, _v_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    r0 = ((_v_0) | (_h_3));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_under)
    Term _ps_0 = r0;
    Term _real_0 = r1;
    WL_OPEN
    if (term_aux(_ps_0) == CID_Nil) {
      term_sink(e, _real_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ps_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _real_0 = term_keep(e, _real_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_1;
        STK(1) = _real_0;
        STK(2) = FID_path_policy_any_under_k114;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_path_policy_any_under_k114, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        e.mem[_t_0 + 1] = _real_0;
        WL_CONT = term_tsk(FID_path_policy_any_under_k114, _t_0);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_path_policy_under)) {
        u64 _t_1 = task_node(e, FID_path_policy_under, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _f_0;
        e.mem[_t_1 + 1] = _real_0;
        return term_tsk(FID_path_policy_under, _t_1);
      }
      r0 = _f_0;
      r1 = _real_0;
      WL_JMP(FID_path_policy_under);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_under_k114)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _real_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_path_policy_any_under_k115;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_any_under_k115, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_any_under_k115, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_under)) {
      u64 _t_3 = task_node(e, FID_path_policy_any_under, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_2;
      e.mem[_t_3 + 1] = _real_1;
      return term_tsk(FID_path_policy_any_under, _t_3);
    }
    r0 = _f_2;
    r1 = _real_1;
    WL_JMP(FID_path_policy_any_under);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_any_under_k115)
    WL_POPN(1);
    u32 _h_2 = STK(0);
    u32 _h_1 = r0;
    WL_OPEN
    r0 = ((_h_2) | (_h_1));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_class_of)
    Term _pol_0 = r0;
    Term _pol_1 = r1;
    Term _pol_2 = r2;
    Term _real_0 = r3;
    WL_OPEN
    Term _v_0 = 0;
    _pol_0 = term_keep(e, _pol_0, 1);
    _pol_1 = term_keep(e, _pol_1, 1);
    _pol_2 = term_keep(e, _pol_2, 1);
    Term _o_0[1];
    if (spin_22(e, _o_0, _pol_0, _pol_1, _pol_2) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    _real_0 = term_keep(e, _real_0, 1);
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _pol_0;
      STK(1) = _pol_1;
      STK(2) = _pol_2;
      STK(3) = _real_0;
      STK(4) = FID_path_policy_class_of_k117;
      WL_PUSHN(5);
    } else {
      u64 _t_0 = task_node(e, FID_path_policy_class_of_k117, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _pol_0;
      e.mem[_t_0 + 1] = _pol_1;
      e.mem[_t_0 + 2] = _pol_2;
      e.mem[_t_0 + 3] = _real_0;
      WL_CONT = term_tsk(FID_path_policy_class_of_k117, _t_0);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_under)) {
      u64 _t_1 = task_node(e, FID_path_policy_any_under, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _v_0;
      e.mem[_t_1 + 1] = _real_0;
      return term_tsk(FID_path_policy_any_under, _t_1);
    }
    r0 = _v_0;
    r1 = _real_0;
    WL_JMP(FID_path_policy_any_under);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_class_of_k117)
    WL_POPN(4);
    Term _pol_3 = STK(0);
    Term _pol_4 = STK(1);
    Term _pol_5 = STK(2);
    Term _real_1 = STK(3);
    u32 _h_0 = r0;
    WL_OPEN
    _pol_3 = term_keep(e, _pol_3, 1);
    _pol_4 = term_keep(e, _pol_4, 1);
    _pol_5 = term_keep(e, _pol_5, 1);
    _real_1 = term_keep(e, _real_1, 1);
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _pol_3;
      STK(1) = _pol_4;
      STK(2) = _pol_5;
      STK(3) = _real_1;
      STK(4) = _h_0;
      STK(5) = FID_path_policy_class_of_k118;
      WL_PUSHN(6);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_class_of_k118, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _pol_3;
      e.mem[_t_2 + 1] = _pol_4;
      e.mem[_t_2 + 2] = _pol_5;
      e.mem[_t_2 + 3] = _real_1;
      e.mem[_t_2 + 4] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_class_of_k118, _t_2);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_protects)) {
      u64 _t_3 = task_node(e, FID_path_policy_protects, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _pol_3;
      e.mem[_t_3 + 1] = _pol_4;
      e.mem[_t_3 + 2] = _pol_5;
      e.mem[_t_3 + 3] = _real_1;
      return term_tsk(FID_path_policy_protects, _t_3);
    }
    r0 = _pol_3;
    r1 = _pol_4;
    r2 = _pol_5;
    r3 = _real_1;
    WL_JMP(FID_path_policy_protects);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_class_of_k118)
    WL_POPN(5);
    Term _pol_6 = STK(0);
    Term _pol_7 = STK(1);
    Term _pol_8 = STK(2);
    Term _real_2 = STK(3);
    u32 _h_2 = STK(4);
    u32 _h_1 = r0;
    WL_OPEN
    Term _v_1 = 0;
    Term _o_1[1];
    if (spin_20(e, _o_1, _pol_6, _pol_7, _pol_8) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _h_2;
      STK(1) = _h_1;
      STK(2) = FID_path_policy_class_of_k119;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_path_policy_class_of_k119, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _h_2;
      e.mem[_t_4 + 1] = _h_1;
      WL_CONT = term_tsk(FID_path_policy_class_of_k119, _t_4);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_root_of)) {
      u64 _t_5 = task_node(e, FID_path_policy_root_of, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _v_1;
      e.mem[_t_5 + 1] = _real_2;
      return term_tsk(FID_path_policy_root_of, _t_5);
    }
    r0 = _v_1;
    r1 = _real_2;
    WL_JMP(FID_path_policy_root_of);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_class_of_k119)
    WL_POPN(2);
    u32 _h_5 = STK(0);
    u32 _h_6 = STK(1);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    WL_OPEN
    u32 _v_2 = 0;
    Term _o_2[1];
    if (spin_36(e, _o_2, _h_3, _h_4) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_2[0];
    Term _o_3[1];
    if (spin_37(e, _o_3, _h_5, _h_6, _v_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_3[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_put)
    Term _fuel_0 = r0;
    Term _t_0 = r1;
    Term _k_0 = r2;
    u32 _z_0 = r3;
    u32 _odd_0 = r4;
    Term _e_0 = r5;
    Term _e_1 = r6;
    Term _e_2 = r7;
    u32 _e_3 = r8;
    Term _e_4 = r9;
    u32 _e_5 = r10;
    Term _e_6 = r11;
    u32 _e_7 = r12;
    Term _e_8 = r13;
    u32 _e_9 = r14;
    Term _e_10 = r15;
    WL_OPEN
    WL_SPIN
    if (_fuel_0 == 0) {
      r0 = _t_0;
      WL_RETN(1);
    } else {
      Term _f_0 = (_fuel_0 - 1);
      if (term_aux(_t_0) == CID_catalog_union_TNil) {
        if (_z_0 == 1) {
          u64 _nd_0 = heap_alloc(e, cls_fit(14));
          e.mem[_nd_0 + 0] = 1;
          e.mem[_nd_0 + 1] = _e_0;
          e.mem[_nd_0 + 2] = _e_1;
          e.mem[_nd_0 + 3] = _e_2;
          e.mem[_nd_0 + 4] = _e_3;
          e.mem[_nd_0 + 5] = _e_4;
          e.mem[_nd_0 + 6] = _e_5;
          e.mem[_nd_0 + 7] = _e_6;
          e.mem[_nd_0 + 8] = _e_7;
          e.mem[_nd_0 + 9] = _e_8;
          e.mem[_nd_0 + 10] = _e_9;
          e.mem[_nd_0 + 11] = _e_10;
          e.mem[_nd_0 + 12] = term_pak(CID_catalog_union_TNil, 0);
          e.mem[_nd_0 + 13] = term_pak(CID_catalog_union_TNil, 0);
          r0 = term_ctr(CID_catalog_union_TNode, _nd_0);
          WL_RETN(1);
        } else {
          if (_odd_0 == 1) {
            Term _v_0 = 0;
            Term _o_0[1];
            if (spin_23(e, _o_0, _k_0) == 0) {
              return 0;
            }
            _v_0 = _o_0[0];
            u32 _v_1 = 0;
            Term _o_1[1];
            if (spin_24(e, _o_1, _v_0) == 0) {
              return 0;
            }
            _v_1 = (u32)_o_1[0];
            u32 _v_2 = 0;
            Term _o_2[1];
            if (spin_25(e, _o_2, _v_0) == 0) {
              return 0;
            }
            _v_2 = (u32)_o_2[0];
            if (seq) {
              WL_ROOM(1, 0);
              STK(0) = FID_catalog_union_put_k134;
              WL_PUSHN(1);
            } else {
              u64 _t_1 = task_node(e, FID_catalog_union_put_k134, WL_CONT, WL_IDX, 1);
              WL_CONT = term_tsk(FID_catalog_union_put_k134, _t_1);
              WL_IDX = 0;
            }
            r0 = _f_0;
            r1 = term_pak(CID_catalog_union_TNil, 0);
            r2 = _v_0;
            r3 = _v_1;
            r4 = _v_2;
            r5 = _e_0;
            r6 = _e_1;
            r7 = _e_2;
            r8 = _e_3;
            r9 = _e_4;
            r10 = _e_5;
            r11 = _e_6;
            r12 = _e_7;
            r13 = _e_8;
            r14 = _e_9;
            r15 = _e_10;
            _fuel_0 = r0;
            _t_0 = r1;
            _k_0 = r2;
            _z_0 = r3;
            _odd_0 = r4;
            _e_0 = r5;
            _e_1 = r6;
            _e_2 = r7;
            _e_3 = r8;
            _e_4 = r9;
            _e_5 = r10;
            _e_6 = r11;
            _e_7 = r12;
            _e_8 = r13;
            _e_9 = r14;
            _e_10 = r15;
            WL_AGAIN(FID_catalog_union_put);
          } else {
            Term _v_3 = 0;
            Term _o_3[1];
            if (spin_23(e, _o_3, _k_0) == 0) {
              return 0;
            }
            _v_3 = _o_3[0];
            u32 _v_4 = 0;
            Term _o_4[1];
            if (spin_24(e, _o_4, _v_3) == 0) {
              return 0;
            }
            _v_4 = (u32)_o_4[0];
            u32 _v_5 = 0;
            Term _o_5[1];
            if (spin_25(e, _o_5, _v_3) == 0) {
              return 0;
            }
            _v_5 = (u32)_o_5[0];
            if (seq) {
              WL_ROOM(1, 0);
              STK(0) = FID_catalog_union_put_k135;
              WL_PUSHN(1);
            } else {
              u64 _t_2 = task_node(e, FID_catalog_union_put_k135, WL_CONT, WL_IDX, 1);
              WL_CONT = term_tsk(FID_catalog_union_put_k135, _t_2);
              WL_IDX = 0;
            }
            r0 = _f_0;
            r1 = term_pak(CID_catalog_union_TNil, 0);
            r2 = _v_3;
            r3 = _v_4;
            r4 = _v_5;
            r5 = _e_0;
            r6 = _e_1;
            r7 = _e_2;
            r8 = _e_3;
            r9 = _e_4;
            r10 = _e_5;
            r11 = _e_6;
            r12 = _e_7;
            r13 = _e_8;
            r14 = _e_9;
            r15 = _e_10;
            _fuel_0 = r0;
            _t_0 = r1;
            _k_0 = r2;
            _z_0 = r3;
            _odd_0 = r4;
            _e_0 = r5;
            _e_1 = r6;
            _e_2 = r7;
            _e_3 = r8;
            _e_4 = r9;
            _e_5 = r10;
            _e_6 = r11;
            _e_7 = r12;
            _e_8 = r13;
            _e_9 = r14;
            _e_10 = r15;
            WL_AGAIN(FID_catalog_union_put);
          }
        }
      } else {
        u64 _sp_0 = term_loc(_t_0);
        u32 _f_1 = e.mem[_sp_0 + 0];
        Term _f_2 = e.mem[_sp_0 + 1];
        Term _f_3 = e.mem[_sp_0 + 2];
        Term _f_4 = e.mem[_sp_0 + 3];
        u32 _f_5 = e.mem[_sp_0 + 4];
        Term _f_6 = e.mem[_sp_0 + 5];
        u32 _f_7 = e.mem[_sp_0 + 6];
        Term _f_8 = e.mem[_sp_0 + 7];
        u32 _f_9 = e.mem[_sp_0 + 8];
        Term _f_10 = e.mem[_sp_0 + 9];
        u32 _f_11 = e.mem[_sp_0 + 10];
        Term _f_12 = e.mem[_sp_0 + 11];
        Term _f_13 = e.mem[_sp_0 + 12];
        Term _f_14 = e.mem[_sp_0 + 13];
        if (_z_0 == 1) {
          u32 _v_6 = 0;
          Term _v_7 = 0;
          Term _v_8 = 0;
          Term _v_9 = 0;
          u32 _v_10 = 0;
          Term _v_11 = 0;
          u32 _v_12 = 0;
          Term _v_13 = 0;
          u32 _v_14 = 0;
          Term _v_15 = 0;
          u32 _v_16 = 0;
          Term _v_17 = 0;
          Term _o_6[12];
          if (spin_40(e, _o_6, _f_1, _f_2, _f_3, _f_4, _f_5, _f_6, _f_7, _f_8, _f_9, _f_10, _f_11, _f_12, _e_0, _e_1, _e_2, _e_3, _e_4, _e_5, _e_6, _e_7, _e_8, _e_9, _e_10) == 0) {
            return 0;
          }
          _v_6 = (u32)_o_6[0];
          _v_7 = _o_6[1];
          _v_8 = _o_6[2];
          _v_9 = _o_6[3];
          _v_10 = (u32)_o_6[4];
          _v_11 = _o_6[5];
          _v_12 = (u32)_o_6[6];
          _v_13 = _o_6[7];
          _v_14 = (u32)_o_6[8];
          _v_15 = _o_6[9];
          _v_16 = (u32)_o_6[10];
          _v_17 = _o_6[11];
          u64 _nd_3 = _sp_0;
          e.mem[_nd_3 + 0] = _v_6;
          e.mem[_nd_3 + 1] = _v_7;
          e.mem[_nd_3 + 2] = _v_8;
          e.mem[_nd_3 + 3] = _v_9;
          e.mem[_nd_3 + 4] = _v_10;
          e.mem[_nd_3 + 5] = _v_11;
          e.mem[_nd_3 + 6] = _v_12;
          e.mem[_nd_3 + 7] = _v_13;
          e.mem[_nd_3 + 8] = _v_14;
          e.mem[_nd_3 + 9] = _v_15;
          e.mem[_nd_3 + 10] = _v_16;
          e.mem[_nd_3 + 11] = _v_17;
          e.mem[_nd_3 + 12] = _f_13;
          e.mem[_nd_3 + 13] = _f_14;
          r0 = term_ctr(CID_catalog_union_TNode, _nd_3);
          WL_RETN(1);
        } else {
          if (_odd_0 == 1) {
            Term _v_30 = 0;
            Term _o_7[1];
            if (spin_23(e, _o_7, _k_0) == 0) {
              return 0;
            }
            _v_30 = _o_7[0];
            u32 _v_31 = 0;
            Term _o_8[1];
            if (spin_24(e, _o_8, _v_30) == 0) {
              return 0;
            }
            _v_31 = (u32)_o_8[0];
            u32 _v_32 = 0;
            Term _o_9[1];
            if (spin_25(e, _o_9, _v_30) == 0) {
              return 0;
            }
            _v_32 = (u32)_o_9[0];
            heap_free(e, cls_fit(14), _sp_0);
            if (seq) {
              WL_ROOM(14, 0);
              STK(0) = _f_1;
              STK(1) = _f_2;
              STK(2) = _f_3;
              STK(3) = _f_4;
              STK(4) = _f_5;
              STK(5) = _f_6;
              STK(6) = _f_7;
              STK(7) = _f_8;
              STK(8) = _f_9;
              STK(9) = _f_10;
              STK(10) = _f_11;
              STK(11) = _f_12;
              STK(12) = _f_13;
              STK(13) = FID_catalog_union_put_k136;
              WL_PUSHN(14);
            } else {
              u64 _t_3 = task_node(e, FID_catalog_union_put_k136, WL_CONT, WL_IDX, 1);
              e.mem[_t_3 + 0] = _f_1;
              e.mem[_t_3 + 1] = _f_2;
              e.mem[_t_3 + 2] = _f_3;
              e.mem[_t_3 + 3] = _f_4;
              e.mem[_t_3 + 4] = _f_5;
              e.mem[_t_3 + 5] = _f_6;
              e.mem[_t_3 + 6] = _f_7;
              e.mem[_t_3 + 7] = _f_8;
              e.mem[_t_3 + 8] = _f_9;
              e.mem[_t_3 + 9] = _f_10;
              e.mem[_t_3 + 10] = _f_11;
              e.mem[_t_3 + 11] = _f_12;
              e.mem[_t_3 + 12] = _f_13;
              WL_CONT = term_tsk(FID_catalog_union_put_k136, _t_3);
              WL_IDX = 13;
            }
            r0 = _f_0;
            r1 = _f_14;
            r2 = _v_30;
            r3 = _v_31;
            r4 = _v_32;
            r5 = _e_0;
            r6 = _e_1;
            r7 = _e_2;
            r8 = _e_3;
            r9 = _e_4;
            r10 = _e_5;
            r11 = _e_6;
            r12 = _e_7;
            r13 = _e_8;
            r14 = _e_9;
            r15 = _e_10;
            _fuel_0 = r0;
            _t_0 = r1;
            _k_0 = r2;
            _z_0 = r3;
            _odd_0 = r4;
            _e_0 = r5;
            _e_1 = r6;
            _e_2 = r7;
            _e_3 = r8;
            _e_4 = r9;
            _e_5 = r10;
            _e_6 = r11;
            _e_7 = r12;
            _e_8 = r13;
            _e_9 = r14;
            _e_10 = r15;
            WL_AGAIN(FID_catalog_union_put);
          } else {
            Term _v_33 = 0;
            Term _o_10[1];
            if (spin_23(e, _o_10, _k_0) == 0) {
              return 0;
            }
            _v_33 = _o_10[0];
            u32 _v_34 = 0;
            Term _o_11[1];
            if (spin_24(e, _o_11, _v_33) == 0) {
              return 0;
            }
            _v_34 = (u32)_o_11[0];
            u32 _v_35 = 0;
            Term _o_12[1];
            if (spin_25(e, _o_12, _v_33) == 0) {
              return 0;
            }
            _v_35 = (u32)_o_12[0];
            heap_free(e, cls_fit(14), _sp_0);
            if (seq) {
              WL_ROOM(14, 0);
              STK(0) = _f_1;
              STK(1) = _f_2;
              STK(2) = _f_3;
              STK(3) = _f_4;
              STK(4) = _f_5;
              STK(5) = _f_6;
              STK(6) = _f_7;
              STK(7) = _f_8;
              STK(8) = _f_9;
              STK(9) = _f_10;
              STK(10) = _f_11;
              STK(11) = _f_12;
              STK(12) = _f_14;
              STK(13) = FID_catalog_union_put_k137;
              WL_PUSHN(14);
            } else {
              u64 _t_4 = task_node(e, FID_catalog_union_put_k137, WL_CONT, WL_IDX, 1);
              e.mem[_t_4 + 0] = _f_1;
              e.mem[_t_4 + 1] = _f_2;
              e.mem[_t_4 + 2] = _f_3;
              e.mem[_t_4 + 3] = _f_4;
              e.mem[_t_4 + 4] = _f_5;
              e.mem[_t_4 + 5] = _f_6;
              e.mem[_t_4 + 6] = _f_7;
              e.mem[_t_4 + 7] = _f_8;
              e.mem[_t_4 + 8] = _f_9;
              e.mem[_t_4 + 9] = _f_10;
              e.mem[_t_4 + 10] = _f_11;
              e.mem[_t_4 + 11] = _f_12;
              e.mem[_t_4 + 12] = _f_14;
              WL_CONT = term_tsk(FID_catalog_union_put_k137, _t_4);
              WL_IDX = 13;
            }
            r0 = _f_0;
            r1 = _f_13;
            r2 = _v_33;
            r3 = _v_34;
            r4 = _v_35;
            r5 = _e_0;
            r6 = _e_1;
            r7 = _e_2;
            r8 = _e_3;
            r9 = _e_4;
            r10 = _e_5;
            r11 = _e_6;
            r12 = _e_7;
            r13 = _e_8;
            r14 = _e_9;
            r15 = _e_10;
            _fuel_0 = r0;
            _t_0 = r1;
            _k_0 = r2;
            _z_0 = r3;
            _odd_0 = r4;
            _e_0 = r5;
            _e_1 = r6;
            _e_2 = r7;
            _e_3 = r8;
            _e_4 = r9;
            _e_5 = r10;
            _e_6 = r11;
            _e_7 = r12;
            _e_8 = r13;
            _e_9 = r14;
            _e_10 = r15;
            WL_AGAIN(FID_catalog_union_put);
          }
        }
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_put_k134)
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_1 = heap_alloc(e, cls_fit(14));
    e.mem[_nd_1 + 0] = 0;
    e.mem[_nd_1 + 1] = 0;
    e.mem[_nd_1 + 2] = 0;
    e.mem[_nd_1 + 3] = 0;
    e.mem[_nd_1 + 4] = 0;
    e.mem[_nd_1 + 5] = 0;
    e.mem[_nd_1 + 6] = 0;
    e.mem[_nd_1 + 7] = 0;
    e.mem[_nd_1 + 8] = 0;
    e.mem[_nd_1 + 9] = 0;
    e.mem[_nd_1 + 10] = 0;
    e.mem[_nd_1 + 11] = 0;
    e.mem[_nd_1 + 12] = term_pak(CID_catalog_union_TNil, 0);
    e.mem[_nd_1 + 13] = _h_0;
    r0 = term_ctr(CID_catalog_union_TNode, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_put_k135)
    Term _h_1 = r0;
    WL_OPEN
    u64 _nd_2 = heap_alloc(e, cls_fit(14));
    e.mem[_nd_2 + 0] = 0;
    e.mem[_nd_2 + 1] = 0;
    e.mem[_nd_2 + 2] = 0;
    e.mem[_nd_2 + 3] = 0;
    e.mem[_nd_2 + 4] = 0;
    e.mem[_nd_2 + 5] = 0;
    e.mem[_nd_2 + 6] = 0;
    e.mem[_nd_2 + 7] = 0;
    e.mem[_nd_2 + 8] = 0;
    e.mem[_nd_2 + 9] = 0;
    e.mem[_nd_2 + 10] = 0;
    e.mem[_nd_2 + 11] = 0;
    e.mem[_nd_2 + 12] = _h_1;
    e.mem[_nd_2 + 13] = term_pak(CID_catalog_union_TNil, 0);
    r0 = term_ctr(CID_catalog_union_TNode, _nd_2);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_put_k136)
    WL_POPN(13);
    u32 _f_15 = STK(0);
    Term _f_16 = STK(1);
    Term _f_17 = STK(2);
    Term _f_18 = STK(3);
    u32 _f_19 = STK(4);
    Term _f_20 = STK(5);
    u32 _f_21 = STK(6);
    Term _f_22 = STK(7);
    u32 _f_23 = STK(8);
    Term _f_24 = STK(9);
    u32 _f_25 = STK(10);
    Term _f_26 = STK(11);
    Term _f_27 = STK(12);
    Term _h_2 = r0;
    WL_OPEN
    u64 _nd_4 = heap_alloc(e, cls_fit(14));
    e.mem[_nd_4 + 0] = _f_15;
    e.mem[_nd_4 + 1] = _f_16;
    e.mem[_nd_4 + 2] = _f_17;
    e.mem[_nd_4 + 3] = _f_18;
    e.mem[_nd_4 + 4] = _f_19;
    e.mem[_nd_4 + 5] = _f_20;
    e.mem[_nd_4 + 6] = _f_21;
    e.mem[_nd_4 + 7] = _f_22;
    e.mem[_nd_4 + 8] = _f_23;
    e.mem[_nd_4 + 9] = _f_24;
    e.mem[_nd_4 + 10] = _f_25;
    e.mem[_nd_4 + 11] = _f_26;
    e.mem[_nd_4 + 12] = _f_27;
    e.mem[_nd_4 + 13] = _h_2;
    r0 = term_ctr(CID_catalog_union_TNode, _nd_4);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_put_k137)
    WL_POPN(13);
    u32 _f_28 = STK(0);
    Term _f_29 = STK(1);
    Term _f_30 = STK(2);
    Term _f_31 = STK(3);
    u32 _f_32 = STK(4);
    Term _f_33 = STK(5);
    u32 _f_34 = STK(6);
    Term _f_35 = STK(7);
    u32 _f_36 = STK(8);
    Term _f_37 = STK(9);
    u32 _f_38 = STK(10);
    Term _f_39 = STK(11);
    Term _f_40 = STK(12);
    Term _h_3 = r0;
    WL_OPEN
    u64 _nd_5 = heap_alloc(e, cls_fit(14));
    e.mem[_nd_5 + 0] = _f_28;
    e.mem[_nd_5 + 1] = _f_29;
    e.mem[_nd_5 + 2] = _f_30;
    e.mem[_nd_5 + 3] = _f_31;
    e.mem[_nd_5 + 4] = _f_32;
    e.mem[_nd_5 + 5] = _f_33;
    e.mem[_nd_5 + 6] = _f_34;
    e.mem[_nd_5 + 7] = _f_35;
    e.mem[_nd_5 + 8] = _f_36;
    e.mem[_nd_5 + 9] = _f_37;
    e.mem[_nd_5 + 10] = _f_38;
    e.mem[_nd_5 + 11] = _f_39;
    e.mem[_nd_5 + 12] = _h_3;
    e.mem[_nd_5 + 13] = _f_40;
    r0 = term_ctr(CID_catalog_union_TNode, _nd_5);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_0)
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
        STK(1) = FID_wire_put_list_go_0_k140;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_0_k140, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_put_list_go_0_k140, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_0);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_0_k140)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_41(e, _o_1, _f_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tiny_up_at)
    Term _chain_0 = r0;
    Term _up_0 = r1;
    WL_OPEN
    if (term_aux(_chain_0) == CID_Nil) {
      term_sink(e, _up_0);
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _chain_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      term_sink(e, _f_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (!DEVICE && !seq && fid_nofk(FID_tiny_elem)) {
        u64 _t_0 = task_node(e, FID_tiny_elem, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _up_0;
        e.mem[_t_0 + 1] = _f_0;
        return term_tsk(FID_tiny_elem, _t_0);
      }
      r0 = _up_0;
      r1 = _f_0;
      WL_JMP(FID_tiny_elem);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tiny_pick_go)
    Term _chain_0 = r0;
    Term _up_0 = r1;
    u32 _hit_0 = r2;
    WL_OPEN
    if (term_aux(_chain_0) == CID_Nil) {
      term_sink(e, _up_0);
      r0 = 1;
      r1 = 0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _chain_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      if (_hit_0 == 1) {
        term_sink(e, _f_1);
        term_sink(e, _up_0);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 0;
        r1 = _f_0;
        WL_RETN(2);
      } else {
        _f_1 = term_keep(e, _f_1, 1);
        _up_0 = term_keep(e, _up_0, 1);
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _f_1;
          STK(1) = _up_0;
          STK(2) = FID_tiny_pick_go_k145;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_tiny_pick_go_k145, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_1;
          e.mem[_t_0 + 1] = _up_0;
          WL_CONT = term_tsk(FID_tiny_pick_go_k145, _t_0);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_tiny_up_at)) {
          u64 _t_1 = task_node(e, FID_tiny_up_at, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _f_1;
          e.mem[_t_1 + 1] = _up_0;
          return term_tsk(FID_tiny_up_at, _t_1);
        }
        r0 = _f_1;
        r1 = _up_0;
        WL_JMP(FID_tiny_up_at);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tiny_pick_go_k145)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _up_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_tiny_pick_go)) {
      u64 _t_2 = task_node(e, FID_tiny_pick_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _f_2;
      e.mem[_t_2 + 1] = _up_1;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_tiny_pick_go, _t_2);
    }
    r0 = _f_2;
    r1 = _up_1;
    r2 = _h_0;
    WL_JMP(FID_tiny_pick_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_fold)
    Term _ns_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ns_0) == CID_Nil) {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ns_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_wire_flat_fold_k147;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_flat_fold_k147, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_flat_fold_k147, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _ns_0 = r0;
      WL_AGAIN(FID_wire_flat_fold);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_fold_k147)
    WL_POPN(1);
    Term _f_2 = STK(0);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_1[4];
    if (spin_42(e, _o_1, _f_2, _h_0, _h_1, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_cells)
    Term _ws_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ws_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ws_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_ffi_gateway_width_cells_k150;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_gateway_width_cells_k150, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_ffi_gateway_width_cells_k150, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _ws_0 = r0;
      WL_AGAIN(FID_ffi_gateway_width_cells);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_cells_k150)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _f_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_Con, _nd_0));
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_all)
    Term _rs_0 = r0;
    Term _ws_0 = r1;
    WL_OPEN
    if (term_aux(_rs_0) == CID_Nil) {
      term_sink(e, _ws_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      _ws_0 = term_keep(e, _ws_0, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_1;
        STK(1) = _ws_0;
        STK(2) = FID_gateway_width_pads_all_k152;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_gateway_width_pads_all_k152, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        e.mem[_t_0 + 1] = _ws_0;
        WL_CONT = term_tsk(FID_gateway_width_pads_all_k152, _t_0);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_gateway_width_pads_row)) {
        u64 _t_1 = task_node(e, FID_gateway_width_pads_row, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _ws_0;
        e.mem[_t_1 + 1] = _f_0;
        return term_tsk(FID_gateway_width_pads_row, _t_1);
      }
      r0 = _ws_0;
      r1 = _f_0;
      WL_JMP(FID_gateway_width_pads_row);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_all_k152)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _ws_1 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_gateway_width_pads_all_k153;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_gateway_width_pads_all_k153, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_gateway_width_pads_all_k153, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_pads_all)) {
      u64 _t_3 = task_node(e, FID_gateway_width_pads_all, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_2;
      e.mem[_t_3 + 1] = _ws_1;
      return term_tsk(FID_gateway_width_pads_all, _t_3);
    }
    r0 = _f_2;
    r1 = _ws_1;
    WL_JMP(FID_gateway_width_pads_all);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_pads_all_k153)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _h_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_1);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_cols)
    Term _rows_0 = r0;
    WL_OPEN
    if (term_aux(_rows_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rows_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_1;
        STK(1) = FID_gateway_width_cols_k155;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_gateway_width_cols_k155, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        WL_CONT = term_tsk(FID_gateway_width_cols_k155, _t_0);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
        u64 _t_1 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _f_0;
        return term_tsk(FID_List_length, _t_1);
      }
      r0 = _f_0;
      WL_JMP(FID_List_length);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_cols_k155)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_gateway_width_cols_k156;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_gateway_width_cols_k156, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_gateway_width_cols_k156, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_cols)) {
      u64 _t_3 = task_node(e, FID_gateway_width_cols, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_2;
      return term_tsk(FID_gateway_width_cols, _t_3);
    }
    r0 = _f_2;
    WL_JMP(FID_gateway_width_cols);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_cols_k156)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    r0 = (_h_2 > _h_1 ? _h_2 : _h_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_widths)
    Term _k_0 = r0;
    u32 _m_0 = r1;
    Term _rows_0 = r2;
    Term _i_0 = r3;
    WL_OPEN
    if (_k_0 == 0) {
      term_sink(e, _rows_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _p_0 = (_k_0 - 1);
      _rows_0 = term_keep(e, _rows_0, 1);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _p_0;
        STK(1) = _m_0;
        STK(2) = _rows_0;
        STK(3) = _i_0;
        STK(4) = FID_gateway_width_widths_k158;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_gateway_width_widths_k158, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _p_0;
        e.mem[_t_0 + 1] = _m_0;
        e.mem[_t_0 + 2] = _rows_0;
        e.mem[_t_0 + 3] = _i_0;
        WL_CONT = term_tsk(FID_gateway_width_widths_k158, _t_0);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_gateway_width_col_w)) {
        u64 _t_1 = task_node(e, FID_gateway_width_col_w, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _rows_0;
        e.mem[_t_1 + 1] = _m_0;
        e.mem[_t_1 + 2] = _i_0;
        return term_tsk(FID_gateway_width_col_w, _t_1);
      }
      r0 = _rows_0;
      r1 = _m_0;
      r2 = _i_0;
      WL_JMP(FID_gateway_width_col_w);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_widths_k158)
    WL_POPN(4);
    Term _p_1 = STK(0);
    u32 _m_1 = STK(1);
    Term _rows_1 = STK(2);
    Term _i_1 = STK(3);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_gateway_width_widths_k159;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_gateway_width_widths_k159, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_gateway_width_widths_k159, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_widths)) {
      u64 _t_3 = task_node(e, FID_gateway_width_widths, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _p_1;
      e.mem[_t_3 + 1] = _m_1;
      e.mem[_t_3 + 2] = _rows_1;
      e.mem[_t_3 + 3] = nat_chk(e, _i_1 + 1);
      return term_tsk(FID_gateway_width_widths, _t_3);
    }
    r0 = _p_1;
    r1 = _m_1;
    r2 = _rows_1;
    r3 = nat_chk(e, _i_1 + 1);
    WL_JMP(FID_gateway_width_widths);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_widths_k159)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _h_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_1);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_flat)
    Term _xss_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xss_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xss_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_wire_flat_flat_k161;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_flat_flat_k161, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_flat_flat_k161, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _xss_0 = r0;
      WL_AGAIN(FID_wire_flat_flat);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_flat_k161)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_flat_one)) {
      u64 _t_1 = task_node(e, FID_wire_flat_one, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _f_2;
      e.mem[_t_1 + 1] = _h_0;
      return term_tsk(FID_wire_flat_one, _t_1);
    }
    r0 = _f_2;
    r1 = _h_0;
    WL_JMP(FID_wire_flat_one);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_put_ns)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_0)) {
      u64 _t_0 = task_node(e, FID_wire_put_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _xs_0;
      e.mem[_t_0 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_0, _t_0);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_0);
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
        STK(3) = FID_wire_cdig_go_k165;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_cdig_go_k165, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _x_0;
        e.mem[_t_0 + 2] = _i_0;
        WL_CONT = term_tsk(FID_wire_cdig_go_k165, _t_0);
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
  WL_CASE(FID_wire_cdig_go_k165)
    WL_POPN(3);
    u32 _f_2 = STK(0);
    u32 _x_1 = STK(1);
    Term _i_1 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_43(e, _o_0, U32_BIN(_x_1, ==, _f_2), _h_0, _h_1, _i_1) == 0) {
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
          STK(3) = FID_wire_get_nat_go_k168;
          WL_PUSHN(4);
        } else {
          u64 _t_1 = task_node(e, FID_wire_get_nat_go_k168, WL_CONT, WL_IDX, 1);
          e.mem[_t_1 + 0] = _j_0;
          e.mem[_t_1 + 1] = _ts_1;
          e.mem[_t_1 + 2] = _ds_0;
          WL_CONT = term_tsk(FID_wire_get_nat_go_k168, _t_1);
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
          STK(1) = FID_wire_get_nat_go_k169;
          WL_PUSHN(2);
        } else {
          u64 _t_4 = task_node(e, FID_wire_get_nat_go_k169, WL_CONT, WL_IDX, 1);
          e.mem[_t_4 + 0] = _ts_2;
          WL_CONT = term_tsk(FID_wire_get_nat_go_k169, _t_4);
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
  WL_CASE(FID_wire_get_nat_go_k168)
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
  WL_CASE(FID_wire_get_nat_go_k169)
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
        STK(1) = FID_wire_get_nat_end_k171;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_get_nat_end_k171, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _ts_2;
        WL_CONT = term_tsk(FID_wire_get_nat_end_k171, _t_0);
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
  WL_CASE(FID_wire_get_nat_end_k171)
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
      STK(0) = FID_wire_get_str_k176;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_str_k176, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_str_k176, _t_0);
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
  WL_CASE(FID_wire_get_str_k176)
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
  WL_CASE(FID_path_policy_holds_at)
    Term _pol_0 = r0;
    Term _pol_1 = r1;
    Term _pol_2 = r2;
    Term _at_0 = r3;
    WL_OPEN
    Term _v_0 = 0;
    _pol_0 = term_keep(e, _pol_0, 1);
    _pol_1 = term_keep(e, _pol_1, 1);
    _pol_2 = term_keep(e, _pol_2, 1);
    Term _o_0[1];
    if (spin_22(e, _o_0, _pol_0, _pol_1, _pol_2) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    _at_0 = term_keep(e, _at_0, 1);
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _pol_0;
      STK(1) = _pol_1;
      STK(2) = _pol_2;
      STK(3) = _at_0;
      STK(4) = FID_path_policy_holds_at_k189;
      WL_PUSHN(5);
    } else {
      u64 _t_0 = task_node(e, FID_path_policy_holds_at_k189, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _pol_0;
      e.mem[_t_0 + 1] = _pol_1;
      e.mem[_t_0 + 2] = _pol_2;
      e.mem[_t_0 + 3] = _at_0;
      WL_CONT = term_tsk(FID_path_policy_holds_at_k189, _t_0);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_under)) {
      u64 _t_1 = task_node(e, FID_path_policy_any_under, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _v_0;
      e.mem[_t_1 + 1] = _at_0;
      return term_tsk(FID_path_policy_any_under, _t_1);
    }
    r0 = _v_0;
    r1 = _at_0;
    WL_JMP(FID_path_policy_any_under);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_holds_at_k189)
    WL_POPN(4);
    Term _pol_3 = STK(0);
    Term _pol_4 = STK(1);
    Term _pol_5 = STK(2);
    Term _at_1 = STK(3);
    u32 _h_0 = r0;
    WL_OPEN
    Term _v_1 = 0;
    Term _o_1[1];
    if (spin_22(e, _o_1, _pol_3, _pol_4, _pol_5) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_path_policy_holds_at_k190;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_holds_at_k190, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_holds_at_k190, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_any_ancestor)) {
      u64 _t_3 = task_node(e, FID_path_policy_any_ancestor, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _v_1;
      e.mem[_t_3 + 1] = _at_1;
      return term_tsk(FID_path_policy_any_ancestor, _t_3);
    }
    r0 = _v_1;
    r1 = _at_1;
    WL_JMP(FID_path_policy_any_ancestor);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_holds_at_k190)
    WL_POPN(1);
    u32 _h_2 = STK(0);
    u32 _h_1 = r0;
    WL_OPEN
    r0 = ((_h_2) | (_h_1));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_class_res)
    Term _pol_0 = r0;
    Term _pol_1 = r1;
    Term _pol_2 = r2;
    Term _r_0 = r3;
    u32 _r_1 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _r_1;
      STK(1) = FID_path_policy_class_res_k192;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_path_policy_class_res_k192, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _r_1;
      WL_CONT = term_tsk(FID_path_policy_class_res_k192, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_class_of)) {
      u64 _t_1 = task_node(e, FID_path_policy_class_of, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _pol_0;
      e.mem[_t_1 + 1] = _pol_1;
      e.mem[_t_1 + 2] = _pol_2;
      e.mem[_t_1 + 3] = _r_0;
      return term_tsk(FID_path_policy_class_of, _t_1);
    }
    r0 = _pol_0;
    r1 = _pol_1;
    r2 = _pol_2;
    r3 = _r_0;
    WL_JMP(FID_path_policy_class_of);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_class_res_k192)
    WL_POPN(1);
    u32 _r_2 = STK(0);
    u32 _h_0 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_45(e, _o_0, _h_0, _r_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_0)
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
          STK(2) = FID_wire_get_list_go_0_k199;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_0_k199, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          WL_CONT = term_tsk(FID_wire_get_list_go_0_k199, _t_0);
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
  WL_CASE(FID_wire_get_list_go_0_k199)
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
      STK(1) = FID_wire_get_list_go_0_k200;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_0_k200, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_3;
      WL_CONT = term_tsk(FID_wire_get_list_go_0_k200, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_0)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      return term_tsk(FID_wire_get_list_go_0, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    WL_JMP(FID_wire_get_list_go_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_0_k200)
    WL_POPN(1);
    Term _cur_4 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_46(e, _o_0, _cur_4, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_ents_of)
    Term _ns_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ns_0) == CID_Nil) {
      r0 = 1;
      r1 = term_pak(CID_Nil, 0);
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ns_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      if (term_aux(_f_1) == CID_Nil) {
        spare_free(e, cls_fit(2), _sp_0);
        r0 = 0;
        r1 = 0;
        WL_RETN(2);
      } else {
        Term _fb_1[2];
        u64 _sp_1 = ctr_take(e, _f_1, 2, _fb_1);
        Term _f_2 = _fb_1[0];
        Term _f_3 = _fb_1[1];
        if (term_aux(_f_3) == CID_Nil) {
          spare_free(e, cls_fit(2), _sp_1);
          spare_free(e, cls_fit(2), _sp_0);
          r0 = 0;
          r1 = 0;
          WL_RETN(2);
        } else {
          Term _fb_2[2];
          u64 _sp_2 = ctr_take(e, _f_3, 2, _fb_2);
          Term _f_4 = _fb_2[0];
          Term _f_5 = _fb_2[1];
          if (term_aux(_f_5) == CID_Nil) {
            spare_free(e, cls_fit(2), _sp_2);
            spare_free(e, cls_fit(2), _sp_1);
            spare_free(e, cls_fit(2), _sp_0);
            r0 = 0;
            r1 = 0;
            WL_RETN(2);
          } else {
            Term _fb_3[2];
            u64 _sp_3 = ctr_take(e, _f_5, 2, _fb_3);
            Term _f_6 = _fb_3[0];
            Term _f_7 = _fb_3[1];
            if (term_aux(_f_7) == CID_Nil) {
              spare_free(e, cls_fit(2), _sp_3);
              spare_free(e, cls_fit(2), _sp_2);
              spare_free(e, cls_fit(2), _sp_1);
              spare_free(e, cls_fit(2), _sp_0);
              r0 = 0;
              r1 = 0;
              WL_RETN(2);
            } else {
              Term _fb_4[2];
              u64 _sp_4 = ctr_take(e, _f_7, 2, _fb_4);
              Term _f_8 = _fb_4[0];
              Term _f_9 = _fb_4[1];
              if (term_aux(_f_9) == CID_Nil) {
                spare_free(e, cls_fit(2), _sp_4);
                spare_free(e, cls_fit(2), _sp_3);
                spare_free(e, cls_fit(2), _sp_2);
                spare_free(e, cls_fit(2), _sp_1);
                spare_free(e, cls_fit(2), _sp_0);
                r0 = 0;
                r1 = 0;
                WL_RETN(2);
              } else {
                Term _fb_5[2];
                u64 _sp_5 = ctr_take(e, _f_9, 2, _fb_5);
                Term _f_10 = _fb_5[0];
                Term _f_11 = _fb_5[1];
                if (term_aux(_f_11) == CID_Nil) {
                  spare_free(e, cls_fit(2), _sp_5);
                  spare_free(e, cls_fit(2), _sp_4);
                  spare_free(e, cls_fit(2), _sp_3);
                  spare_free(e, cls_fit(2), _sp_2);
                  spare_free(e, cls_fit(2), _sp_1);
                  spare_free(e, cls_fit(2), _sp_0);
                  r0 = 0;
                  r1 = 0;
                  WL_RETN(2);
                } else {
                  Term _fb_6[2];
                  u64 _sp_6 = ctr_take(e, _f_11, 2, _fb_6);
                  Term _f_12 = _fb_6[0];
                  Term _f_13 = _fb_6[1];
                  spare_free(e, cls_fit(2), _sp_6);
                  spare_free(e, cls_fit(2), _sp_5);
                  spare_free(e, cls_fit(2), _sp_4);
                  spare_free(e, cls_fit(2), _sp_3);
                  spare_free(e, cls_fit(2), _sp_2);
                  spare_free(e, cls_fit(2), _sp_1);
                  spare_free(e, cls_fit(2), _sp_0);
                  if (seq) {
                    WL_ROOM(8, 0);
                    STK(0) = _f_0;
                    STK(1) = _f_2;
                    STK(2) = _f_4;
                    STK(3) = _f_6;
                    STK(4) = _f_8;
                    STK(5) = _f_10;
                    STK(6) = _f_12;
                    STK(7) = FID_ffi_catalog_union_ents_of_k202;
                    WL_PUSHN(8);
                  } else {
                    u64 _t_0 = task_node(e, FID_ffi_catalog_union_ents_of_k202, WL_CONT, WL_IDX, 1);
                    e.mem[_t_0 + 0] = _f_0;
                    e.mem[_t_0 + 1] = _f_2;
                    e.mem[_t_0 + 2] = _f_4;
                    e.mem[_t_0 + 3] = _f_6;
                    e.mem[_t_0 + 4] = _f_8;
                    e.mem[_t_0 + 5] = _f_10;
                    e.mem[_t_0 + 6] = _f_12;
                    WL_CONT = term_tsk(FID_ffi_catalog_union_ents_of_k202, _t_0);
                    WL_IDX = 7;
                  }
                  r0 = _f_13;
                  _ns_0 = r0;
                  WL_AGAIN(FID_ffi_catalog_union_ents_of);
                }
              }
            }
          }
        }
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_ents_of_k202)
    WL_POPN(7);
    Term _f_14 = STK(0);
    Term _f_15 = STK(1);
    Term _f_16 = STK(2);
    Term _f_17 = STK(3);
    Term _f_18 = STK(4);
    Term _f_19 = STK(5);
    Term _f_20 = STK(6);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    Term _v_1 = 0;
    Term _o_0[2];
    if (spin_47(e, _o_0, _f_17) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    _v_1 = _o_0[1];
    u32 _v_3 = 0;
    Term _v_4 = 0;
    Term _o_1[2];
    if (spin_47(e, _o_1, _f_18) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_1[0];
    _v_4 = _o_1[1];
    u32 _v_5 = 0;
    Term _v_6 = 0;
    Term _o_2[2];
    if (spin_47(e, _o_2, _f_19) == 0) {
      return 0;
    }
    _v_5 = (u32)_o_2[0];
    _v_6 = _o_2[1];
    u32 _v_7 = 0;
    Term _v_8 = 0;
    Term _o_3[2];
    if (spin_47(e, _o_3, _f_20) == 0) {
      return 0;
    }
    _v_7 = (u32)_o_3[0];
    _v_8 = _o_3[1];
    Term _o_4[2];
    if (spin_48(e, _o_4, _f_14, _f_15, _f_16, _v_0, _v_1, _v_3, _v_4, _v_5, _v_6, _v_7, _v_8, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = (u32)_o_4[0];
    r1 = _o_4[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_extra_t)
    Term _cs_0 = r0;
    Term _bt_0 = r1;
    u32 _seen_0 = r2;
    WL_OPEN
    WL_SPIN
    if (term_aux(_cs_0) == CID_Nil) {
      term_sink(e, _bt_0);
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _cs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[11];
      u64 _sp_1 = ctr_take(e, _f_0, 11, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      u32 _f_5 = _fb_1[3];
      Term _f_6 = _fb_1[4];
      u32 _f_7 = _fb_1[5];
      Term _f_8 = _fb_1[6];
      u32 _f_9 = _fb_1[7];
      Term _f_10 = _fb_1[8];
      u32 _f_11 = _fb_1[9];
      Term _f_12 = _fb_1[10];
      spare_free(e, cls_fit(11), _sp_1);
      if (_seen_0 == 1) {
        u32 _v_0 = 0;
        Term _o_3[1];
        if (spin_52(e, _o_3, _f_1, _bt_0) == 0) {
          return 0;
        }
        _v_0 = (u32)_o_3[0];
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _bt_0;
        r2 = _v_0;
        _cs_0 = r0;
        _bt_0 = r1;
        _seen_0 = r2;
        WL_AGAIN(FID_catalog_union_extra_t);
      } else {
        u32 _v_14 = 0;
        Term _o_4[1];
        if (spin_52(e, _o_4, _f_1, _bt_0) == 0) {
          return 0;
        }
        _v_14 = (u32)_o_4[0];
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(12, 0);
          STK(0) = _f_2;
          STK(1) = _f_3;
          STK(2) = _f_4;
          STK(3) = _f_5;
          STK(4) = _f_6;
          STK(5) = _f_7;
          STK(6) = _f_8;
          STK(7) = _f_9;
          STK(8) = _f_10;
          STK(9) = _f_11;
          STK(10) = _f_12;
          STK(11) = FID_catalog_union_extra_t_k206;
          WL_PUSHN(12);
        } else {
          u64 _t_0 = task_node(e, FID_catalog_union_extra_t_k206, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_2;
          e.mem[_t_0 + 1] = _f_3;
          e.mem[_t_0 + 2] = _f_4;
          e.mem[_t_0 + 3] = _f_5;
          e.mem[_t_0 + 4] = _f_6;
          e.mem[_t_0 + 5] = _f_7;
          e.mem[_t_0 + 6] = _f_8;
          e.mem[_t_0 + 7] = _f_9;
          e.mem[_t_0 + 8] = _f_10;
          e.mem[_t_0 + 9] = _f_11;
          e.mem[_t_0 + 10] = _f_12;
          WL_CONT = term_tsk(FID_catalog_union_extra_t_k206, _t_0);
          WL_IDX = 11;
        }
        r0 = _f_1;
        r1 = _bt_0;
        r2 = _v_14;
        _cs_0 = r0;
        _bt_0 = r1;
        _seen_0 = r2;
        WL_AGAIN(FID_catalog_union_extra_t);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_extra_t_k206)
    WL_POPN(11);
    Term _f_26 = STK(0);
    Term _f_27 = STK(1);
    Term _f_28 = STK(2);
    u32 _f_29 = STK(3);
    Term _f_30 = STK(4);
    u32 _f_31 = STK(5);
    Term _f_32 = STK(6);
    u32 _f_33 = STK(7);
    Term _f_34 = STK(8);
    u32 _f_35 = STK(9);
    Term _f_36 = STK(10);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(11));
    e.mem[_nd_0 + 0] = rfc_seal(e, _f_26);
    e.mem[_nd_0 + 1] = rfc_seal(e, _f_27);
    e.mem[_nd_0 + 2] = rfc_seal(e, _f_28);
    e.mem[_nd_0 + 3] = rfc_seal(e, _f_29);
    e.mem[_nd_0 + 4] = rfc_seal(e, _f_30);
    e.mem[_nd_0 + 5] = rfc_seal(e, _f_31);
    e.mem[_nd_0 + 6] = rfc_seal(e, _f_32);
    e.mem[_nd_0 + 7] = rfc_seal(e, _f_33);
    e.mem[_nd_0 + 8] = rfc_seal(e, _f_34);
    e.mem[_nd_0 + 9] = rfc_seal(e, _f_35);
    e.mem[_nd_0 + 10] = rfc_seal(e, _f_36);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_catalog_union_Ent, _nd_0));
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_bundled_t)
    Term _bs_0 = r0;
    Term _ct_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_bs_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _bs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[11];
      u64 _sp_1 = ctr_take(e, _f_0, 11, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      u32 _f_5 = _fb_1[3];
      Term _f_6 = _fb_1[4];
      u32 _f_7 = _fb_1[5];
      Term _f_8 = _fb_1[6];
      u32 _f_9 = _fb_1[7];
      Term _f_10 = _fb_1[8];
      u32 _f_11 = _fb_1[9];
      Term _f_12 = _fb_1[10];
      spare_free(e, cls_fit(11), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(13, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = _f_5;
        STK(4) = _f_6;
        STK(5) = _f_7;
        STK(6) = _f_8;
        STK(7) = _f_9;
        STK(8) = _f_10;
        STK(9) = _f_11;
        STK(10) = _f_12;
        STK(11) = _ct_0;
        STK(12) = FID_catalog_union_bundled_t_k208;
        WL_PUSHN(13);
      } else {
        u64 _t_0 = task_node(e, FID_catalog_union_bundled_t_k208, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        e.mem[_t_0 + 3] = _f_5;
        e.mem[_t_0 + 4] = _f_6;
        e.mem[_t_0 + 5] = _f_7;
        e.mem[_t_0 + 6] = _f_8;
        e.mem[_t_0 + 7] = _f_9;
        e.mem[_t_0 + 8] = _f_10;
        e.mem[_t_0 + 9] = _f_11;
        e.mem[_t_0 + 10] = _f_12;
        e.mem[_t_0 + 11] = _ct_0;
        WL_CONT = term_tsk(FID_catalog_union_bundled_t_k208, _t_0);
        WL_IDX = 12;
      }
      r0 = _f_1;
      r1 = _ct_0;
      _bs_0 = r0;
      _ct_0 = r1;
      WL_AGAIN(FID_catalog_union_bundled_t);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_bundled_t_k208)
    WL_POPN(12);
    Term _f_13 = STK(0);
    Term _f_14 = STK(1);
    Term _f_15 = STK(2);
    u32 _f_16 = STK(3);
    Term _f_17 = STK(4);
    u32 _f_18 = STK(5);
    Term _f_19 = STK(6);
    u32 _f_20 = STK(7);
    Term _f_21 = STK(8);
    u32 _f_22 = STK(9);
    Term _f_23 = STK(10);
    Term _ct_1 = STK(11);
    Term _h_0 = r0;
    WL_OPEN
    Term _v_0 = 0;
    Term _v_1 = 0;
    Term _v_2 = 0;
    u32 _v_3 = 0;
    Term _v_4 = 0;
    u32 _v_5 = 0;
    Term _v_6 = 0;
    u32 _v_7 = 0;
    Term _v_8 = 0;
    u32 _v_9 = 0;
    Term _v_10 = 0;
    u32 _v_11 = 0;
    Term _v_12 = 0;
    Term _v_13 = 0;
    Term _v_14 = 0;
    u32 _v_15 = 0;
    Term _v_16 = 0;
    u32 _v_17 = 0;
    Term _v_18 = 0;
    u32 _v_19 = 0;
    Term _v_20 = 0;
    u32 _v_21 = 0;
    Term _v_22 = 0;
    Term _v_23 = 0;
    Term _o_0[1];
    if (spin_49(e, _o_0, _f_13, _f_14, _f_15, _f_16, _f_17, _f_18, _f_19, _f_20, _f_21, _f_22, _f_23) == 0) {
      return 0;
    }
    _v_23 = _o_0[0];
    Term _o_1[12];
    if (spin_50(e, _o_1, _ct_1, _v_23) == 0) {
      return 0;
    }
    _v_11 = (u32)_o_1[0];
    _v_12 = _o_1[1];
    _v_13 = _o_1[2];
    _v_14 = _o_1[3];
    _v_15 = (u32)_o_1[4];
    _v_16 = _o_1[5];
    _v_17 = (u32)_o_1[6];
    _v_18 = _o_1[7];
    _v_19 = (u32)_o_1[8];
    _v_20 = _o_1[9];
    _v_21 = (u32)_o_1[10];
    _v_22 = _o_1[11];
    Term _o_3[11];
    if (spin_53(e, _o_3, _f_13, _f_14, _f_15, _f_16, _f_17, _f_18, _f_19, _f_20, _f_21, _f_22, _f_23, _v_11, _v_12, _v_13, _v_14, _v_15, _v_16, _v_17, _v_18, _v_19, _v_20, _v_21, _v_22) == 0) {
      return 0;
    }
    _v_0 = _o_3[0];
    _v_1 = _o_3[1];
    _v_2 = _o_3[2];
    _v_3 = (u32)_o_3[3];
    _v_4 = _o_3[4];
    _v_5 = (u32)_o_3[5];
    _v_6 = _o_3[6];
    _v_7 = (u32)_o_3[7];
    _v_8 = _o_3[8];
    _v_9 = (u32)_o_3[9];
    _v_10 = _o_3[10];
    u64 _nd_0 = heap_alloc(e, cls_fit(11));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, _v_1);
    e.mem[_nd_0 + 2] = rfc_seal(e, _v_2);
    e.mem[_nd_0 + 3] = rfc_seal(e, _v_3);
    e.mem[_nd_0 + 4] = rfc_seal(e, _v_4);
    e.mem[_nd_0 + 5] = rfc_seal(e, _v_5);
    e.mem[_nd_0 + 6] = rfc_seal(e, _v_6);
    e.mem[_nd_0 + 7] = rfc_seal(e, _v_7);
    e.mem[_nd_0 + 8] = rfc_seal(e, _v_8);
    e.mem[_nd_0 + 9] = rfc_seal(e, _v_9);
    e.mem[_nd_0 + 10] = rfc_seal(e, _v_10);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_catalog_union_Ent, _nd_0));
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
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
        STK(1) = FID_List_append_k210;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_List_append_k210, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_List_append_k210, _t_0);
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
  WL_CASE(FID_List_append_k210)
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
  WL_CASE(FID_catalog_union_tab)
    Term _xs_0 = r0;
    Term _t_0 = r1;
    WL_OPEN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = _t_0;
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _xs_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      Term _f_3 = e.mem[_sp_1 + 1];
      Term _f_4 = e.mem[_sp_1 + 2];
      u32 _f_5 = e.mem[_sp_1 + 3];
      Term _f_6 = e.mem[_sp_1 + 4];
      u32 _f_7 = e.mem[_sp_1 + 5];
      Term _f_8 = e.mem[_sp_1 + 6];
      u32 _f_9 = e.mem[_sp_1 + 7];
      Term _f_10 = e.mem[_sp_1 + 8];
      u32 _f_11 = e.mem[_sp_1 + 9];
      Term _f_12 = e.mem[_sp_1 + 10];
      Term _v_0 = 0;
      Term _o_0[1];
      if (spin_49(e, _o_0, _f_2, _f_3, _f_4, _f_5, _f_6, _f_7, _f_8, _f_9, _f_10, _f_11, _f_12) == 0) {
        return 0;
      }
      _v_0 = _o_0[0];
      u32 _v_1 = 0;
      Term _o_1[1];
      if (spin_24(e, _o_1, _v_0) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      u32 _v_2 = 0;
      Term _o_2[1];
      if (spin_25(e, _o_2, _v_0) == 0) {
        return 0;
      }
      _v_2 = (u32)_o_2[0];
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_1;
        STK(1) = FID_catalog_union_tab_k212;
        WL_PUSHN(2);
      } else {
        u64 _t_1 = task_node(e, FID_catalog_union_tab_k212, WL_CONT, WL_IDX, 1);
        e.mem[_t_1 + 0] = _f_1;
        WL_CONT = term_tsk(FID_catalog_union_tab_k212, _t_1);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_catalog_union_put)) {
        u64 _t_2 = task_node(e, FID_catalog_union_put, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = nat_chk(e, _v_0 + 1);
        e.mem[_t_2 + 1] = _t_0;
        e.mem[_t_2 + 2] = _v_0;
        e.mem[_t_2 + 3] = _v_1;
        e.mem[_t_2 + 4] = _v_2;
        e.mem[_t_2 + 5] = _f_2;
        e.mem[_t_2 + 6] = _f_3;
        e.mem[_t_2 + 7] = _f_4;
        e.mem[_t_2 + 8] = _f_5;
        e.mem[_t_2 + 9] = _f_6;
        e.mem[_t_2 + 10] = _f_7;
        e.mem[_t_2 + 11] = _f_8;
        e.mem[_t_2 + 12] = _f_9;
        e.mem[_t_2 + 13] = _f_10;
        e.mem[_t_2 + 14] = _f_11;
        e.mem[_t_2 + 15] = _f_12;
        return term_tsk(FID_catalog_union_put, _t_2);
      }
      r0 = nat_chk(e, _v_0 + 1);
      r1 = _t_0;
      r2 = _v_0;
      r3 = _v_1;
      r4 = _v_2;
      r5 = _f_2;
      r6 = _f_3;
      r7 = _f_4;
      r8 = _f_5;
      r9 = _f_6;
      r10 = _f_7;
      r11 = _f_8;
      r12 = _f_9;
      r13 = _f_10;
      r14 = _f_11;
      r15 = _f_12;
      WL_JMP(FID_catalog_union_put);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_tab_k212)
    WL_POPN(1);
    Term _f_13 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_catalog_union_tab)) {
      u64 _t_3 = task_node(e, FID_catalog_union_tab, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_13;
      e.mem[_t_3 + 1] = _h_0;
      return term_tsk(FID_catalog_union_tab, _t_3);
    }
    r0 = _f_13;
    r1 = _h_0;
    WL_JMP(FID_catalog_union_tab);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_0)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_0_k215;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_0_k215, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_0_k215, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_0)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _xs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_0, _t_1);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_0_k215)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[1];
    if (spin_54(e, _o_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
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
  WL_CASE(FID_tiny_pick)
    Term _chain_0 = r0;
    Term _up_0 = r1;
    WL_OPEN
    _chain_0 = term_keep(e, _chain_0, 1);
    _up_0 = term_keep(e, _up_0, 1);
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _chain_0;
      STK(1) = _up_0;
      STK(2) = FID_tiny_pick_k220;
      WL_PUSHN(3);
    } else {
      u64 _t_0 = task_node(e, FID_tiny_pick_k220, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _chain_0;
      e.mem[_t_0 + 1] = _up_0;
      WL_CONT = term_tsk(FID_tiny_pick_k220, _t_0);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_tiny_up_at)) {
      u64 _t_1 = task_node(e, FID_tiny_up_at, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _chain_0;
      e.mem[_t_1 + 1] = _up_0;
      return term_tsk(FID_tiny_up_at, _t_1);
    }
    r0 = _chain_0;
    r1 = _up_0;
    WL_JMP(FID_tiny_up_at);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_tiny_pick_k220)
    WL_POPN(2);
    Term _chain_1 = STK(0);
    Term _up_1 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_tiny_pick_go)) {
      u64 _t_2 = task_node(e, FID_tiny_pick_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _chain_1;
      e.mem[_t_2 + 1] = _up_1;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_tiny_pick_go, _t_2);
    }
    r0 = _chain_1;
    r1 = _up_1;
    r2 = _h_0;
    WL_JMP(FID_tiny_pick_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_unflat)
    Term _ns_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_flat_unflat_k223;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_flat_unflat_k223, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_flat_unflat_k223, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_flat_fold)) {
      u64 _t_1 = task_node(e, FID_wire_flat_fold, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _ns_0;
      return term_tsk(FID_wire_flat_fold, _t_1);
    }
    r0 = _ns_0;
    WL_JMP(FID_wire_flat_fold);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_flat_unflat_k223)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_1[2];
    if (spin_56(e, _o_1, _h_0, _h_1, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_table)
    Term _rows_0 = r0;
    WL_OPEN
    if (term_aux(_rows_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rows_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_1;
        STK(1) = FID_ffi_gateway_width_table_k226;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_gateway_width_table_k226, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        WL_CONT = term_tsk(FID_ffi_gateway_width_table_k226, _t_0);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_gateway_width_cells)) {
        u64 _t_1 = task_node(e, FID_ffi_gateway_width_cells, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _f_0;
        return term_tsk(FID_ffi_gateway_width_cells, _t_1);
      }
      r0 = _f_0;
      WL_JMP(FID_ffi_gateway_width_cells);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_table_k226)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_ffi_gateway_width_table_k227;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_ffi_gateway_width_table_k227, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_ffi_gateway_width_table_k227, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_gateway_width_table)) {
      u64 _t_3 = task_node(e, FID_ffi_gateway_width_table, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _f_2;
      return term_tsk(FID_ffi_gateway_width_table, _t_3);
    }
    r0 = _f_2;
    WL_JMP(FID_ffi_gateway_width_table);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_table_k227)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _h_2);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_1);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_layout)
    Term _rows_0 = r0;
    WL_OPEN
    _rows_0 = term_keep(e, _rows_0, 1);
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _rows_0;
      STK(1) = FID_gateway_width_layout_k229;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_gateway_width_layout_k229, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _rows_0;
      WL_CONT = term_tsk(FID_gateway_width_layout_k229, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_cols)) {
      u64 _t_1 = task_node(e, FID_gateway_width_cols, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _rows_0;
      return term_tsk(FID_gateway_width_cols, _t_1);
    }
    r0 = _rows_0;
    WL_JMP(FID_gateway_width_cols);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_layout_k229)
    WL_POPN(1);
    Term _rows_1 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    _rows_1 = term_keep(e, _rows_1, 1);
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _rows_1;
      STK(1) = FID_gateway_width_layout_k230;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_gateway_width_layout_k230, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _rows_1;
      WL_CONT = term_tsk(FID_gateway_width_layout_k230, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_widths)) {
      u64 _t_3 = task_node(e, FID_gateway_width_widths, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _h_0;
      e.mem[_t_3 + 1] = 0;
      e.mem[_t_3 + 2] = _rows_1;
      e.mem[_t_3 + 3] = 0;
      return term_tsk(FID_gateway_width_widths, _t_3);
    }
    r0 = _h_0;
    r1 = 0;
    r2 = _rows_1;
    r3 = 0;
    WL_JMP(FID_gateway_width_widths);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_layout_k230)
    WL_POPN(1);
    Term _rows_2 = STK(0);
    Term _ws_0 = r0;
    WL_OPEN
    _ws_0 = term_keep(e, _ws_0, 1);
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _ws_0;
      STK(1) = FID_gateway_width_layout_k231;
      WL_PUSHN(2);
    } else {
      u64 _t_4 = task_node(e, FID_gateway_width_layout_k231, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _ws_0;
      WL_CONT = term_tsk(FID_gateway_width_layout_k231, _t_4);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_pads_all)) {
      u64 _t_5 = task_node(e, FID_gateway_width_pads_all, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _rows_2;
      e.mem[_t_5 + 1] = _ws_0;
      return term_tsk(FID_gateway_width_pads_all, _t_5);
    }
    r0 = _rows_2;
    r1 = _ws_0;
    WL_JMP(FID_gateway_width_pads_all);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_gateway_width_layout_k231)
    WL_POPN(1);
    Term _ws_1 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    r0 = _ws_1;
    r1 = _h_1;
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_tok)
    u32 _c_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _c_0;
      STK(1) = FID_wire_tok_k236;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_wire_tok_k236, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _c_0;
      WL_CONT = term_tsk(FID_wire_tok_k236, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_cdig_go)) {
      u64 _t_1 = task_node(e, FID_wire_cdig_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = term_ctr(CID_Con, STAT_OFF + 62);
      e.mem[_t_1 + 1] = _c_0;
      e.mem[_t_1 + 2] = 0;
      return term_tsk(FID_wire_cdig_go, _t_1);
    }
    r0 = term_ctr(CID_Con, STAT_OFF + 62);
    r1 = _c_0;
    r2 = 0;
    WL_JMP(FID_wire_cdig_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_tok_k236)
    WL_POPN(1);
    u32 _c_1 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_57(e, _o_1, _h_0, _h_1, U32_BIN(_c_1, ==, 44ull)) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_judge)
    Term _pol_0 = r0;
    Term _pol_1 = r1;
    Term _pol_2 = r2;
    Term _r_0 = r3;
    u32 _r_1 = r4;
    WL_OPEN
    _pol_0 = term_keep(e, _pol_0, 1);
    _pol_1 = term_keep(e, _pol_1, 1);
    _pol_2 = term_keep(e, _pol_2, 1);
    _r_0 = term_keep(e, _r_0, 1);
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _pol_0;
      STK(1) = _pol_1;
      STK(2) = _pol_2;
      STK(3) = _r_0;
      STK(4) = _r_1;
      STK(5) = FID_path_policy_judge_k253;
      WL_PUSHN(6);
    } else {
      u64 _t_0 = task_node(e, FID_path_policy_judge_k253, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _pol_0;
      e.mem[_t_0 + 1] = _pol_1;
      e.mem[_t_0 + 2] = _pol_2;
      e.mem[_t_0 + 3] = _r_0;
      e.mem[_t_0 + 4] = _r_1;
      WL_CONT = term_tsk(FID_path_policy_judge_k253, _t_0);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_class_res)) {
      u64 _t_1 = task_node(e, FID_path_policy_class_res, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _pol_0;
      e.mem[_t_1 + 1] = _pol_1;
      e.mem[_t_1 + 2] = _pol_2;
      e.mem[_t_1 + 3] = _r_0;
      e.mem[_t_1 + 4] = _r_1;
      return term_tsk(FID_path_policy_class_res, _t_1);
    }
    r0 = _pol_0;
    r1 = _pol_1;
    r2 = _pol_2;
    r3 = _r_0;
    r4 = _r_1;
    WL_JMP(FID_path_policy_class_res);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_judge_k253)
    WL_POPN(5);
    Term _pol_3 = STK(0);
    Term _pol_4 = STK(1);
    Term _pol_5 = STK(2);
    Term _r_2 = STK(3);
    u32 _r_3 = STK(4);
    u32 _h_0 = r0;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_59(e, _o_0, _r_2, _r_3) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_path_policy_judge_k254;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_path_policy_judge_k254, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_path_policy_judge_k254, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_path_policy_holds_at)) {
      u64 _t_3 = task_node(e, FID_path_policy_holds_at, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _pol_3;
      e.mem[_t_3 + 1] = _pol_4;
      e.mem[_t_3 + 2] = _pol_5;
      e.mem[_t_3 + 3] = _v_0;
      return term_tsk(FID_path_policy_holds_at, _t_3);
    }
    r0 = _pol_3;
    r1 = _pol_4;
    r2 = _pol_5;
    r3 = _v_0;
    WL_JMP(FID_path_policy_holds_at);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_path_policy_judge_k254)
    WL_POPN(1);
    u32 _h_2 = STK(0);
    u32 _h_1 = r0;
    WL_OPEN
    r0 = _h_2;
    r1 = _h_1;
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_tools_segs)
    Term _cs_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_cs_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _cs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_ffi_tools_segs_k257;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_tools_segs_k257, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_ffi_tools_segs_k257, _t_0);
        WL_IDX = 1;
      }
      r0 = _f_1;
      _cs_0 = r0;
      WL_AGAIN(FID_ffi_tools_segs);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_tools_segs_k257)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _v_1 = 0;
    Term _o_0[2];
    if (spin_61(e, _o_0, _f_2) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    _v_1 = _o_0[1];
    Term _b_0 = 0;
    if (_v_0 == 0) {
      u64 _nd_0 = heap_alloc(e, cls_fit(1));
      e.mem[_nd_0 + 0] = rfc_seal(e, _v_1);
      _b_0 = term_ctr(CID_tools_Name, _nd_0);
    } else if (_v_0 == 1) {
      _b_0 = term_pak(CID_tools_Up, 0);
    } else {
      _b_0 = term_pak(CID_tools_Here, 0);
    }
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _b_0);
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_fast)
    Term _bs_0 = r0;
    Term _cs_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _bs_0;
      STK(1) = _cs_0;
      STK(2) = FID_catalog_union_fast_k268;
      WL_PUSHN(3);
    } else {
      u64 _t_0 = task_node(e, FID_catalog_union_fast_k268, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _bs_0;
      e.mem[_t_0 + 1] = _cs_0;
      WL_CONT = term_tsk(FID_catalog_union_fast_k268, _t_0);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_catalog_union_tab)) {
      u64 _t_1 = task_node(e, FID_catalog_union_tab, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _bs_0;
      e.mem[_t_1 + 1] = term_pak(CID_catalog_union_TNil, 0);
      return term_tsk(FID_catalog_union_tab, _t_1);
    }
    r0 = _bs_0;
    r1 = term_pak(CID_catalog_union_TNil, 0);
    WL_JMP(FID_catalog_union_tab);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_fast_k268)
    WL_POPN(2);
    Term _bs_1 = STK(0);
    Term _cs_1 = STK(1);
    Term _bt_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _bs_1;
      STK(1) = _cs_1;
      STK(2) = _bt_0;
      STK(3) = FID_catalog_union_fast_k269;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_catalog_union_fast_k269, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _bs_1;
      e.mem[_t_2 + 1] = _cs_1;
      e.mem[_t_2 + 2] = _bt_0;
      WL_CONT = term_tsk(FID_catalog_union_fast_k269, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_catalog_union_tab)) {
      u64 _t_3 = task_node(e, FID_catalog_union_tab, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _cs_1;
      e.mem[_t_3 + 1] = term_pak(CID_catalog_union_TNil, 0);
      return term_tsk(FID_catalog_union_tab, _t_3);
    }
    r0 = _cs_1;
    r1 = term_pak(CID_catalog_union_TNil, 0);
    WL_JMP(FID_catalog_union_tab);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_fast_k269)
    WL_POPN(3);
    Term _bs_2 = STK(0);
    Term _cs_2 = STK(1);
    Term _bt_1 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _cs_2;
      STK(1) = _bt_1;
      STK(2) = _h_0;
      STK(3) = FID_catalog_union_fast_k270;
      WL_PUSHN(4);
    } else {
      u64 _t_4 = task_node(e, FID_catalog_union_fast_k270, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _cs_2;
      e.mem[_t_4 + 1] = _bt_1;
      e.mem[_t_4 + 2] = _h_0;
      WL_CONT = term_tsk(FID_catalog_union_fast_k270, _t_4);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_catalog_union_bundled_t)) {
      u64 _t_5 = task_node(e, FID_catalog_union_bundled_t, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _bs_2;
      e.mem[_t_5 + 1] = _h_0;
      return term_tsk(FID_catalog_union_bundled_t, _t_5);
    }
    r0 = _bs_2;
    r1 = _h_0;
    WL_JMP(FID_catalog_union_bundled_t);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_fast_k270)
    WL_POPN(3);
    Term _cs_3 = STK(0);
    Term _bt_2 = STK(1);
    Term _h_2 = STK(2);
    Term _h_1 = r0;
    WL_OPEN
    term_sink(e, _h_2);
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_52(e, _o_0, _cs_3, _bt_2) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_1;
      STK(1) = FID_catalog_union_fast_k271;
      WL_PUSHN(2);
    } else {
      u64 _t_6 = task_node(e, FID_catalog_union_fast_k271, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _h_1;
      WL_CONT = term_tsk(FID_catalog_union_fast_k271, _t_6);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_catalog_union_extra_t)) {
      u64 _t_7 = task_node(e, FID_catalog_union_extra_t, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _cs_3;
      e.mem[_t_7 + 1] = _bt_2;
      e.mem[_t_7 + 2] = _v_0;
      return term_tsk(FID_catalog_union_extra_t, _t_7);
    }
    r0 = _cs_3;
    r1 = _bt_2;
    r2 = _v_0;
    WL_JMP(FID_catalog_union_extra_t);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_catalog_union_fast_k271)
    WL_POPN(1);
    Term _h_4 = STK(0);
    Term _h_3 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_List_append)) {
      u64 _t_8 = task_node(e, FID_List_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_8 + 0] = _h_4;
      e.mem[_t_8 + 1] = _h_3;
      return term_tsk(FID_List_append, _t_8);
    }
    r0 = _h_4;
    r1 = _h_3;
    WL_JMP(FID_List_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_ents)
    Term _es_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_es_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _es_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[11];
      u64 _sp_1 = ctr_take(e, _f_0, 11, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      u32 _f_5 = _fb_1[3];
      Term _f_6 = _fb_1[4];
      u32 _f_7 = _fb_1[5];
      Term _f_8 = _fb_1[6];
      u32 _f_9 = _fb_1[7];
      Term _f_10 = _fb_1[8];
      u32 _f_11 = _fb_1[9];
      Term _f_12 = _fb_1[10];
      spare_free(e, cls_fit(11), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(12, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = _f_5;
        STK(4) = _f_6;
        STK(5) = _f_7;
        STK(6) = _f_8;
        STK(7) = _f_9;
        STK(8) = _f_10;
        STK(9) = _f_11;
        STK(10) = _f_12;
        STK(11) = FID_ffi_catalog_union_ents_k273;
        WL_PUSHN(12);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_catalog_union_ents_k273, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        e.mem[_t_0 + 3] = _f_5;
        e.mem[_t_0 + 4] = _f_6;
        e.mem[_t_0 + 5] = _f_7;
        e.mem[_t_0 + 6] = _f_8;
        e.mem[_t_0 + 7] = _f_9;
        e.mem[_t_0 + 8] = _f_10;
        e.mem[_t_0 + 9] = _f_11;
        e.mem[_t_0 + 10] = _f_12;
        WL_CONT = term_tsk(FID_ffi_catalog_union_ents_k273, _t_0);
        WL_IDX = 11;
      }
      r0 = _f_1;
      _es_0 = r0;
      WL_AGAIN(FID_ffi_catalog_union_ents);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_ents_k273)
    WL_POPN(11);
    Term _f_13 = STK(0);
    Term _f_14 = STK(1);
    Term _f_15 = STK(2);
    u32 _f_16 = STK(3);
    Term _f_17 = STK(4);
    u32 _f_18 = STK(5);
    Term _f_19 = STK(6);
    u32 _f_20 = STK(7);
    Term _f_21 = STK(8);
    u32 _f_22 = STK(9);
    Term _f_23 = STK(10);
    Term _h_0 = r0;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_64(e, _o_0, _f_16, _f_17) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    Term _v_1 = 0;
    Term _o_1[1];
    if (spin_64(e, _o_1, _f_18, _f_19) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    Term _v_2 = 0;
    Term _o_2[1];
    if (spin_64(e, _o_2, _f_20, _f_21) == 0) {
      return 0;
    }
    _v_2 = _o_2[0];
    Term _v_3 = 0;
    Term _o_3[1];
    if (spin_64(e, _o_3, _f_22, _f_23) == 0) {
      return 0;
    }
    _v_3 = _o_3[0];
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_3);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_0);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _v_2);
    e.mem[_nd_1 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_0));
    u64 _nd_2 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_2 + 0] = rfc_seal(e, _v_1);
    e.mem[_nd_2 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_1));
    u64 _nd_3 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_3 + 0] = rfc_seal(e, _v_0);
    e.mem[_nd_3 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_2));
    u64 _nd_4 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_4 + 0] = rfc_seal(e, _f_15);
    e.mem[_nd_4 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_3));
    u64 _nd_5 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_5 + 0] = rfc_seal(e, _f_14);
    e.mem[_nd_5 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_4));
    u64 _nd_6 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_6 + 0] = rfc_seal(e, _f_13);
    e.mem[_nd_6 + 1] = rfc_seal(e, term_ctr(CID_Con, _nd_5));
    r0 = term_ctr(CID_Con, _nd_6);
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
        if (spin_55(e, _o_0, _a_1, _a_2) == 0) {
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
  WL_CASE(FID_ffi_tiny_get_ids)
    Term _s_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
      u64 _t_0 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_0, _t_0);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_0);
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
        STK(1) = FID_wire_peek_k291;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_peek_k291, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        WL_CONT = term_tsk(FID_wire_peek_k291, _t_0);
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
  WL_CASE(FID_wire_peek_k291)
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
      STK(0) = FID_wire_get_u32_k296;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_u32_k296, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_u32_k296, _t_0);
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
  WL_CASE(FID_wire_get_u32_k296)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_2[3];
    if (spin_68(e, _o_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_ns)
    Term _s_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
      u64 _t_0 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_0 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_0, _t_0);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_0)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_0_k318;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_0_k318, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_0_k318, _t_0);
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
  WL_CASE(FID_wire_get_list_0_k318)
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
          STK(1) = FID_wire_get_list_0_k319;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_0_k319, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_0_k319, _t_2);
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
  WL_CASE(FID_wire_get_list_0_k319)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_0)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      return term_tsk(FID_wire_get_list_go_0, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    WL_JMP(FID_wire_get_list_go_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_U32_show)
    u32 _a_0 = r0;
    WL_OPEN
    u32 _s_0 = U32_BIN(_a_0, ==, 0);
    if (_s_0 == 1) {
      r0 = term_ctr(CID_SCon, STAT_OFF + 66);
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
    if (spin_55(e, _o_0, _a_1, _a_2) == 0) {
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
        STK(1) = FID_String_append_k331;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_String_append_k331, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_String_append_k331, _t_0);
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
  WL_CASE(FID_String_append_k331)
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
  WL_CASE(FID_ffi_tiny_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_tiny_get_req_k333;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_tiny_get_req_k333, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_tiny_get_req_k333, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_tiny_get_ids)) {
      u64 _t_1 = task_node(e, FID_ffi_tiny_get_ids, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_ffi_tiny_get_ids, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_ffi_tiny_get_ids);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_tiny_get_req_k333)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_tiny_get_req_k334;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_tiny_get_req_k334, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_tiny_get_req_k334, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_tiny_get_ids)) {
        u64 _t_3 = task_node(e, FID_ffi_tiny_get_ids, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_tiny_get_ids, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_tiny_get_ids);
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
  WL_CASE(FID_ffi_tiny_get_req_k334)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_65(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_ffi_gateway_width_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_gateway_width_get_req_k338;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_gateway_width_get_req_k338, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_gateway_width_get_req_k338, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
      u64 _t_1 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_0, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_get_req_k338)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_2;
        STK(1) = FID_ffi_gateway_width_get_req_k339;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_gateway_width_get_req_k339, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_2;
        WL_CONT = term_tsk(FID_ffi_gateway_width_get_req_k339, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_flat_unflat)) {
        u64 _t_3 = task_node(e, FID_wire_flat_unflat, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_1;
        return term_tsk(FID_wire_flat_unflat, _t_3);
      }
      r0 = _h_1;
      WL_JMP(FID_wire_flat_unflat);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_gateway_width_get_req_k339)
    WL_POPN(1);
    Term _h_5 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    WL_OPEN
    Term _o_0[3];
    if (spin_67(e, _o_0, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_nat_k346;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_nat_k346, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_nat_k346, _t_0);
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
  WL_CASE(FID_wire_get_nat_k346)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_wire_get_nat_k347;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_wire_get_nat_k347, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_wire_get_nat_k347, _t_2);
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
  WL_CASE(FID_wire_get_nat_k347)
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
        e.mem[_t_4 + 3] = term_ctr(CID_Con, STAT_OFF + 64);
        return term_tsk(FID_wire_get_nat_end, _t_4);
      }
      r0 = _h_3;
      r1 = _h_4;
      r2 = _h_5;
      r3 = term_ctr(CID_Con, STAT_OFF + 64);
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
  WL_CASE(FID_ffi_path_policy_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_path_policy_get_req_k355;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_path_policy_get_req_k355, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k355, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_get_ns)) {
      u64 _t_1 = task_node(e, FID_ffi_path_policy_get_ns, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_ffi_path_policy_get_ns, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_ffi_path_policy_get_ns);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k355)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_path_policy_get_req_k356;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_path_policy_get_req_k356, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k356, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_get_ns)) {
        u64 _t_3 = task_node(e, FID_ffi_path_policy_get_ns, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_path_policy_get_ns, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_path_policy_get_ns);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k356)
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
        STK(2) = FID_ffi_path_policy_get_req_k357;
        WL_PUSHN(3);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_path_policy_get_req_k357, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_6;
        e.mem[_t_4 + 1] = _h_4;
        WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k357, _t_4);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_get_ns)) {
        u64 _t_5 = task_node(e, FID_ffi_path_policy_get_ns, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_ffi_path_policy_get_ns, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_ffi_path_policy_get_ns);
    } else {
      term_sink(e, _h_6);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k357)
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
        STK(3) = FID_ffi_path_policy_get_req_k358;
        WL_PUSHN(4);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_path_policy_get_req_k358, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _h_10;
        e.mem[_t_6 + 1] = _h_11;
        e.mem[_t_6 + 2] = _h_8;
        WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k358, _t_6);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_get_ns)) {
        u64 _t_7 = task_node(e, FID_ffi_path_policy_get_ns, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _h_9;
        return term_tsk(FID_ffi_path_policy_get_ns, _t_7);
      }
      r0 = _h_9;
      WL_JMP(FID_ffi_path_policy_get_ns);
    } else {
      term_sink(e, _h_10);
      term_sink(e, _h_11);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k358)
    WL_POPN(3);
    Term _h_15 = STK(0);
    Term _h_16 = STK(1);
    Term _h_17 = STK(2);
    u32 _h_12 = r0;
    Term _h_13 = r1;
    Term _h_14 = r2;
    WL_OPEN
    if (_h_12 == 0) {
      u32 _v_0 = 0;
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _o_0[3];
      if (spin_32(e, _o_0, _h_14) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      _v_1 = (u32)_o_0[1];
      _v_2 = _o_0[2];
      if (_v_0 == 0) {
        if (seq) {
          WL_ROOM(6, 0);
          STK(0) = _h_16;
          STK(1) = _h_17;
          STK(2) = _h_13;
          STK(3) = _v_1;
          STK(4) = _v_2;
          STK(5) = FID_ffi_path_policy_get_req_k359;
          WL_PUSHN(6);
        } else {
          u64 _t_8 = task_node(e, FID_ffi_path_policy_get_req_k359, WL_CONT, WL_IDX, 1);
          e.mem[_t_8 + 0] = _h_16;
          e.mem[_t_8 + 1] = _h_17;
          e.mem[_t_8 + 2] = _h_13;
          e.mem[_t_8 + 3] = _v_1;
          e.mem[_t_8 + 4] = _v_2;
          WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k359, _t_8);
          WL_IDX = 5;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_flat_unflat)) {
          u64 _t_9 = task_node(e, FID_wire_flat_unflat, WL_CONT, WL_IDX, 0);
          e.mem[_t_9 + 0] = _h_15;
          return term_tsk(FID_wire_flat_unflat, _t_9);
        }
        r0 = _h_15;
        WL_JMP(FID_wire_flat_unflat);
      } else {
        term_sink(e, _h_15);
        term_sink(e, _h_16);
        term_sink(e, _h_17);
        term_sink(e, _h_13);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = 0;
        WL_RETN(7);
      }
    } else {
      term_sink(e, _h_15);
      term_sink(e, _h_16);
      term_sink(e, _h_17);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k359)
    WL_POPN(5);
    Term _h_20 = STK(0);
    Term _h_21 = STK(1);
    Term _h_22 = STK(2);
    u32 _v_3 = STK(3);
    Term _v_4 = STK(4);
    u32 _h_18 = r0;
    Term _h_19 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(7, 0);
      STK(0) = _h_21;
      STK(1) = _h_22;
      STK(2) = _v_3;
      STK(3) = _v_4;
      STK(4) = _h_18;
      STK(5) = _h_19;
      STK(6) = FID_ffi_path_policy_get_req_k360;
      WL_PUSHN(7);
    } else {
      u64 _t_10 = task_node(e, FID_ffi_path_policy_get_req_k360, WL_CONT, WL_IDX, 1);
      e.mem[_t_10 + 0] = _h_21;
      e.mem[_t_10 + 1] = _h_22;
      e.mem[_t_10 + 2] = _v_3;
      e.mem[_t_10 + 3] = _v_4;
      e.mem[_t_10 + 4] = _h_18;
      e.mem[_t_10 + 5] = _h_19;
      WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k360, _t_10);
      WL_IDX = 6;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_flat_unflat)) {
      u64 _t_11 = task_node(e, FID_wire_flat_unflat, WL_CONT, WL_IDX, 0);
      e.mem[_t_11 + 0] = _h_20;
      return term_tsk(FID_wire_flat_unflat, _t_11);
    }
    r0 = _h_20;
    WL_JMP(FID_wire_flat_unflat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k360)
    WL_POPN(6);
    Term _h_25 = STK(0);
    Term _h_26 = STK(1);
    u32 _v_5 = STK(2);
    Term _v_6 = STK(3);
    u32 _h_27 = STK(4);
    Term _h_28 = STK(5);
    u32 _h_23 = r0;
    Term _h_24 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(7, 0);
      STK(0) = _h_25;
      STK(1) = _h_26;
      STK(2) = _v_5;
      STK(3) = _v_6;
      STK(4) = _h_27;
      STK(5) = _h_28;
      STK(6) = FID_ffi_path_policy_get_req_k361;
      WL_PUSHN(7);
    } else {
      u64 _t_12 = task_node(e, FID_ffi_path_policy_get_req_k361, WL_CONT, WL_IDX, 1);
      e.mem[_t_12 + 0] = _h_25;
      e.mem[_t_12 + 1] = _h_26;
      e.mem[_t_12 + 2] = _v_5;
      e.mem[_t_12 + 3] = _v_6;
      e.mem[_t_12 + 4] = _h_27;
      e.mem[_t_12 + 5] = _h_28;
      WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k361, _t_12);
      WL_IDX = 6;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_get_req_rules)) {
      u64 _t_13 = task_node(e, FID_ffi_path_policy_get_req_rules, WL_CONT, WL_IDX, 0);
      e.mem[_t_13 + 0] = _h_23;
      e.mem[_t_13 + 1] = _h_24;
      return term_tsk(FID_ffi_path_policy_get_req_rules, _t_13);
    }
    r0 = _h_23;
    r1 = _h_24;
    WL_JMP(FID_ffi_path_policy_get_req_rules);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k361)
    WL_POPN(6);
    Term _h_31 = STK(0);
    Term _h_32 = STK(1);
    u32 _v_7 = STK(2);
    Term _v_8 = STK(3);
    u32 _h_33 = STK(4);
    Term _h_34 = STK(5);
    u32 _h_29 = r0;
    Term _h_30 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(8, 0);
      STK(0) = _h_32;
      STK(1) = _v_7;
      STK(2) = _v_8;
      STK(3) = _h_33;
      STK(4) = _h_34;
      STK(5) = _h_29;
      STK(6) = _h_30;
      STK(7) = FID_ffi_path_policy_get_req_k362;
      WL_PUSHN(8);
    } else {
      u64 _t_14 = task_node(e, FID_ffi_path_policy_get_req_k362, WL_CONT, WL_IDX, 1);
      e.mem[_t_14 + 0] = _h_32;
      e.mem[_t_14 + 1] = _v_7;
      e.mem[_t_14 + 2] = _v_8;
      e.mem[_t_14 + 3] = _h_33;
      e.mem[_t_14 + 4] = _h_34;
      e.mem[_t_14 + 5] = _h_29;
      e.mem[_t_14 + 6] = _h_30;
      WL_CONT = term_tsk(FID_ffi_path_policy_get_req_k362, _t_14);
      WL_IDX = 7;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_flat_unflat)) {
      u64 _t_15 = task_node(e, FID_wire_flat_unflat, WL_CONT, WL_IDX, 0);
      e.mem[_t_15 + 0] = _h_31;
      return term_tsk(FID_wire_flat_unflat, _t_15);
    }
    r0 = _h_31;
    WL_JMP(FID_wire_flat_unflat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_path_policy_get_req_k362)
    WL_POPN(7);
    Term _h_37 = STK(0);
    u32 _v_9 = STK(1);
    Term _v_10 = STK(2);
    u32 _h_38 = STK(3);
    Term _h_39 = STK(4);
    u32 _h_40 = STK(5);
    Term _h_41 = STK(6);
    u32 _h_35 = r0;
    Term _h_36 = r1;
    WL_OPEN
    Term _o_1[7];
    if (spin_18(e, _o_1, _h_38, _h_39, _h_40, _h_41, _h_35, _h_36, _h_37, _v_9, _v_10) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = _o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = (u32)_o_1[5];
    r6 = _o_1[6];
    WL_RETN(7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_tools_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_tools_get_req_k366;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_tools_get_req_k366, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_tools_get_req_k366, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
      u64 _t_1 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_0, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_tools_get_req_k366)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_2;
        STK(1) = FID_ffi_tools_get_req_k367;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_tools_get_req_k367, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_2;
        WL_CONT = term_tsk(FID_ffi_tools_get_req_k367, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_tools_segs)) {
        u64 _t_3 = task_node(e, FID_ffi_tools_segs, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_1;
        return term_tsk(FID_ffi_tools_segs, _t_3);
      }
      r0 = _h_1;
      WL_JMP(FID_ffi_tools_segs);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      WL_RETN(3);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_tools_get_req_k367)
    WL_POPN(1);
    Term _h_4 = STK(0);
    Term _h_3 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _h_3;
    r2 = _h_4;
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_catalog_union_get_req_k371;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_catalog_union_get_req_k371, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_catalog_union_get_req_k371, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
      u64 _t_1 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_list_0, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_list_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_get_req_k371)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_catalog_union_get_req_k372;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_catalog_union_get_req_k372, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_catalog_union_get_req_k372, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
        u64 _t_3 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_list_0, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_list_0);
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
  WL_CASE(FID_ffi_catalog_union_get_req_k372)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_4;
        STK(1) = _h_5;
        STK(2) = FID_ffi_catalog_union_get_req_k373;
        WL_PUSHN(3);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_catalog_union_get_req_k373, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_4;
        e.mem[_t_4 + 1] = _h_5;
        WL_CONT = term_tsk(FID_ffi_catalog_union_get_req_k373, _t_4);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_catalog_union_ents_of)) {
        u64 _t_5 = task_node(e, FID_ffi_catalog_union_ents_of, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_6;
        return term_tsk(FID_ffi_catalog_union_ents_of, _t_5);
      }
      r0 = _h_6;
      WL_JMP(FID_ffi_catalog_union_ents_of);
    } else {
      term_sink(e, _h_6);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_get_req_k373)
    WL_POPN(2);
    Term _h_9 = STK(0);
    Term _h_10 = STK(1);
    u32 _h_7 = r0;
    Term _h_8 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _h_10;
      STK(1) = _h_7;
      STK(2) = _h_8;
      STK(3) = FID_ffi_catalog_union_get_req_k374;
      WL_PUSHN(4);
    } else {
      u64 _t_6 = task_node(e, FID_ffi_catalog_union_get_req_k374, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _h_10;
      e.mem[_t_6 + 1] = _h_7;
      e.mem[_t_6 + 2] = _h_8;
      WL_CONT = term_tsk(FID_ffi_catalog_union_get_req_k374, _t_6);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_catalog_union_ents_of)) {
      u64 _t_7 = task_node(e, FID_ffi_catalog_union_ents_of, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _h_9;
      return term_tsk(FID_ffi_catalog_union_ents_of, _t_7);
    }
    r0 = _h_9;
    WL_JMP(FID_ffi_catalog_union_ents_of);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_catalog_union_get_req_k374)
    WL_POPN(3);
    Term _h_13 = STK(0);
    u32 _h_14 = STK(1);
    Term _h_15 = STK(2);
    u32 _h_11 = r0;
    Term _h_12 = r1;
    WL_OPEN
    Term _o_0[4];
    if (spin_63(e, _o_0, _h_14, _h_15, _h_11, _h_12, _h_13) == 0) {
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
        STK(3) = FID_ffi_echo_step_k381;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_echo_step_k381, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _s_1;
        e.mem[_t_0 + 1] = _s_2;
        e.mem[_t_0 + 2] = _input_0;
        WL_CONT = term_tsk(FID_ffi_echo_step_k381, _t_0);
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
      r3 = term_ctr(CID_SCon, STAT_OFF + 424);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k381)
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
      STK(3) = FID_ffi_echo_step_k382;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_ffi_echo_step_k382, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _s_3;
      e.mem[_t_2 + 1] = _input_1;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_ffi_echo_step_k382, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_String_append)) {
      u64 _t_3 = task_node(e, FID_String_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = term_ctr(CID_SCon, STAT_OFF + 368);
      e.mem[_t_3 + 1] = _s_4;
      return term_tsk(FID_String_append, _t_3);
    }
    r0 = term_ctr(CID_SCon, STAT_OFF + 368);
    r1 = _s_4;
    WL_JMP(FID_String_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k382)
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
      STK(2) = FID_ffi_echo_step_k383;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_echo_step_k383, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _s_5;
      e.mem[_t_4 + 1] = _input_2;
      WL_CONT = term_tsk(FID_ffi_echo_step_k383, _t_4);
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
  WL_CASE(FID_ffi_echo_step_k383)
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
  WL_CASE(FID_ffi_echo_open)
    Term _input_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_echo_open_k414;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_echo_open_k414, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_echo_open_k414, _t_0);
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
  WL_CASE(FID_ffi_echo_open_k414)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    if (_h_0 == 1) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_echo_open_k415;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_echo_open_k415, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_echo_open_k415, _t_2);
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
      r3 = term_ctr(CID_SCon, STAT_OFF + 366);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_open_k415)
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
        STK(0) = FID_step_go_k418;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_step_go_k418, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_step_go_k418, _t_0);
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
    } else {
      term_sink(e, _input_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = term_ctr(CID_SCon, STAT_OFF + 454);
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_go_k418)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_73(e, _o_0, _h_0, _h_1, _h_2, _h_3) == 0) {
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
  WL_CASE(FID_ffi_go)
    u32 _entry_0 = r0;
    Term _input_0 = r1;
    WL_OPEN
    if (_entry_0 == 0) {
      Term _o_0[1];
      if (spin_74(e, _o_0, _input_0) == 0) {
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
      if (spin_31(e, _o_1, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_1[0];
      WL_RETN(1);
    } else if (_entry_0 == 4) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k421;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_go_k421, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k421, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_catalog_union_get_req)) {
        u64 _t_1 = task_node(e, FID_ffi_catalog_union_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_ffi_catalog_union_get_req, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_catalog_union_get_req);
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
      Term _o_5[1];
      if (spin_31(e, _o_5, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_5[0];
      WL_RETN(1);
    } else if (_entry_0 == 2) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k424;
        WL_PUSHN(1);
      } else {
        u64 _t_7 = task_node(e, FID_ffi_go_k424, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k424, _t_7);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_tools_get_req)) {
        u64 _t_8 = task_node(e, FID_ffi_tools_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_8 + 0] = _input_0;
        return term_tsk(FID_ffi_tools_get_req, _t_8);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_tools_get_req);
    } else if ((_entry_0 & 7) == 2) {
      u32 _132_0 = ((_entry_0 >> 3) & 1);
      u32 _133_0 = ((_entry_0 >> 4) & 1);
      u32 _133_1 = ((_entry_0 >> 5) & 1);
      u32 _133_2 = ((_entry_0 >> 6) & 1);
      u32 _133_3 = ((_entry_0 >> 7) & 1);
      u32 _133_4 = ((_entry_0 >> 8) & 1);
      u32 _133_5 = ((_entry_0 >> 9) & 1);
      u32 _133_6 = ((_entry_0 >> 10) & 1);
      u32 _133_7 = ((_entry_0 >> 11) & 1);
      u32 _133_8 = ((_entry_0 >> 12) & 1);
      u32 _133_9 = ((_entry_0 >> 13) & 1);
      u32 _133_10 = ((_entry_0 >> 14) & 1);
      u32 _133_11 = ((_entry_0 >> 15) & 1);
      u32 _133_12 = ((_entry_0 >> 16) & 1);
      u32 _133_13 = ((_entry_0 >> 17) & 1);
      u32 _133_14 = ((_entry_0 >> 18) & 1);
      u32 _133_15 = ((_entry_0 >> 19) & 1);
      u32 _133_16 = ((_entry_0 >> 20) & 1);
      u32 _133_17 = ((_entry_0 >> 21) & 1);
      u32 _133_18 = ((_entry_0 >> 22) & 1);
      u32 _133_19 = ((_entry_0 >> 23) & 1);
      u32 _133_20 = ((_entry_0 >> 24) & 1);
      u32 _133_21 = ((_entry_0 >> 25) & 1);
      u32 _133_22 = ((_entry_0 >> 26) & 1);
      u32 _133_23 = ((_entry_0 >> 27) & 1);
      u32 _133_24 = ((_entry_0 >> 28) & 1);
      u32 _133_25 = ((_entry_0 >> 29) & 1);
      u32 _133_26 = ((_entry_0 >> 30) & 1);
      u32 _133_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_12[1];
      if (spin_31(e, _o_12, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_12[0];
      WL_RETN(1);
    } else if (_entry_0 == 6) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k426;
        WL_PUSHN(1);
      } else {
        u64 _t_11 = task_node(e, FID_ffi_go_k426, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k426, _t_11);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_path_policy_get_req)) {
        u64 _t_12 = task_node(e, FID_ffi_path_policy_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_12 + 0] = _input_0;
        return term_tsk(FID_ffi_path_policy_get_req, _t_12);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_path_policy_get_req);
    } else if ((_entry_0 & 7) == 6) {
      u32 _190_0 = ((_entry_0 >> 3) & 1);
      u32 _191_0 = ((_entry_0 >> 4) & 1);
      u32 _191_1 = ((_entry_0 >> 5) & 1);
      u32 _191_2 = ((_entry_0 >> 6) & 1);
      u32 _191_3 = ((_entry_0 >> 7) & 1);
      u32 _191_4 = ((_entry_0 >> 8) & 1);
      u32 _191_5 = ((_entry_0 >> 9) & 1);
      u32 _191_6 = ((_entry_0 >> 10) & 1);
      u32 _191_7 = ((_entry_0 >> 11) & 1);
      u32 _191_8 = ((_entry_0 >> 12) & 1);
      u32 _191_9 = ((_entry_0 >> 13) & 1);
      u32 _191_10 = ((_entry_0 >> 14) & 1);
      u32 _191_11 = ((_entry_0 >> 15) & 1);
      u32 _191_12 = ((_entry_0 >> 16) & 1);
      u32 _191_13 = ((_entry_0 >> 17) & 1);
      u32 _191_14 = ((_entry_0 >> 18) & 1);
      u32 _191_15 = ((_entry_0 >> 19) & 1);
      u32 _191_16 = ((_entry_0 >> 20) & 1);
      u32 _191_17 = ((_entry_0 >> 21) & 1);
      u32 _191_18 = ((_entry_0 >> 22) & 1);
      u32 _191_19 = ((_entry_0 >> 23) & 1);
      u32 _191_20 = ((_entry_0 >> 24) & 1);
      u32 _191_21 = ((_entry_0 >> 25) & 1);
      u32 _191_22 = ((_entry_0 >> 26) & 1);
      u32 _191_23 = ((_entry_0 >> 27) & 1);
      u32 _191_24 = ((_entry_0 >> 28) & 1);
      u32 _191_25 = ((_entry_0 >> 29) & 1);
      u32 _191_26 = ((_entry_0 >> 30) & 1);
      u32 _191_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_17[1];
      if (spin_31(e, _o_17, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_17[0];
      WL_RETN(1);
    } else if (_entry_0 == 1) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k428;
        WL_PUSHN(1);
      } else {
        u64 _t_15 = task_node(e, FID_ffi_go_k428, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k428, _t_15);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_16 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_16 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_16);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else if ((_entry_0 & 7) == 1) {
      u32 _252_0 = ((_entry_0 >> 3) & 1);
      u32 _253_0 = ((_entry_0 >> 4) & 1);
      u32 _253_1 = ((_entry_0 >> 5) & 1);
      u32 _253_2 = ((_entry_0 >> 6) & 1);
      u32 _253_3 = ((_entry_0 >> 7) & 1);
      u32 _253_4 = ((_entry_0 >> 8) & 1);
      u32 _253_5 = ((_entry_0 >> 9) & 1);
      u32 _253_6 = ((_entry_0 >> 10) & 1);
      u32 _253_7 = ((_entry_0 >> 11) & 1);
      u32 _253_8 = ((_entry_0 >> 12) & 1);
      u32 _253_9 = ((_entry_0 >> 13) & 1);
      u32 _253_10 = ((_entry_0 >> 14) & 1);
      u32 _253_11 = ((_entry_0 >> 15) & 1);
      u32 _253_12 = ((_entry_0 >> 16) & 1);
      u32 _253_13 = ((_entry_0 >> 17) & 1);
      u32 _253_14 = ((_entry_0 >> 18) & 1);
      u32 _253_15 = ((_entry_0 >> 19) & 1);
      u32 _253_16 = ((_entry_0 >> 20) & 1);
      u32 _253_17 = ((_entry_0 >> 21) & 1);
      u32 _253_18 = ((_entry_0 >> 22) & 1);
      u32 _253_19 = ((_entry_0 >> 23) & 1);
      u32 _253_20 = ((_entry_0 >> 24) & 1);
      u32 _253_21 = ((_entry_0 >> 25) & 1);
      u32 _253_22 = ((_entry_0 >> 26) & 1);
      u32 _253_23 = ((_entry_0 >> 27) & 1);
      u32 _253_24 = ((_entry_0 >> 28) & 1);
      u32 _253_25 = ((_entry_0 >> 29) & 1);
      u32 _253_26 = ((_entry_0 >> 30) & 1);
      u32 _253_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_28[1];
      if (spin_31(e, _o_28, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_28[0];
      WL_RETN(1);
    } else if (_entry_0 == 5) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k434;
        WL_PUSHN(1);
      } else {
        u64 _t_27 = task_node(e, FID_ffi_go_k434, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k434, _t_27);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_gateway_width_get_req)) {
        u64 _t_28 = task_node(e, FID_ffi_gateway_width_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_28 + 0] = _input_0;
        return term_tsk(FID_ffi_gateway_width_get_req, _t_28);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_gateway_width_get_req);
    } else if ((_entry_0 & 7) == 5) {
      u32 _310_0 = ((_entry_0 >> 3) & 1);
      u32 _311_0 = ((_entry_0 >> 4) & 1);
      u32 _311_1 = ((_entry_0 >> 5) & 1);
      u32 _311_2 = ((_entry_0 >> 6) & 1);
      u32 _311_3 = ((_entry_0 >> 7) & 1);
      u32 _311_4 = ((_entry_0 >> 8) & 1);
      u32 _311_5 = ((_entry_0 >> 9) & 1);
      u32 _311_6 = ((_entry_0 >> 10) & 1);
      u32 _311_7 = ((_entry_0 >> 11) & 1);
      u32 _311_8 = ((_entry_0 >> 12) & 1);
      u32 _311_9 = ((_entry_0 >> 13) & 1);
      u32 _311_10 = ((_entry_0 >> 14) & 1);
      u32 _311_11 = ((_entry_0 >> 15) & 1);
      u32 _311_12 = ((_entry_0 >> 16) & 1);
      u32 _311_13 = ((_entry_0 >> 17) & 1);
      u32 _311_14 = ((_entry_0 >> 18) & 1);
      u32 _311_15 = ((_entry_0 >> 19) & 1);
      u32 _311_16 = ((_entry_0 >> 20) & 1);
      u32 _311_17 = ((_entry_0 >> 21) & 1);
      u32 _311_18 = ((_entry_0 >> 22) & 1);
      u32 _311_19 = ((_entry_0 >> 23) & 1);
      u32 _311_20 = ((_entry_0 >> 24) & 1);
      u32 _311_21 = ((_entry_0 >> 25) & 1);
      u32 _311_22 = ((_entry_0 >> 26) & 1);
      u32 _311_23 = ((_entry_0 >> 27) & 1);
      u32 _311_24 = ((_entry_0 >> 28) & 1);
      u32 _311_25 = ((_entry_0 >> 29) & 1);
      u32 _311_26 = ((_entry_0 >> 30) & 1);
      u32 _311_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_32[1];
      if (spin_31(e, _o_32, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_32[0];
      WL_RETN(1);
    } else if (_entry_0 == 3) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k439;
        WL_PUSHN(1);
      } else {
        u64 _t_38 = task_node(e, FID_ffi_go_k439, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k439, _t_38);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_tiny_get_req)) {
        u64 _t_39 = task_node(e, FID_ffi_tiny_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_39 + 0] = _input_0;
        return term_tsk(FID_ffi_tiny_get_req, _t_39);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_tiny_get_req);
    } else {
      u32 _368_0 = ((_entry_0 >> 2) & 1);
      u32 _369_0 = ((_entry_0 >> 3) & 1);
      u32 _369_1 = ((_entry_0 >> 4) & 1);
      u32 _369_2 = ((_entry_0 >> 5) & 1);
      u32 _369_3 = ((_entry_0 >> 6) & 1);
      u32 _369_4 = ((_entry_0 >> 7) & 1);
      u32 _369_5 = ((_entry_0 >> 8) & 1);
      u32 _369_6 = ((_entry_0 >> 9) & 1);
      u32 _369_7 = ((_entry_0 >> 10) & 1);
      u32 _369_8 = ((_entry_0 >> 11) & 1);
      u32 _369_9 = ((_entry_0 >> 12) & 1);
      u32 _369_10 = ((_entry_0 >> 13) & 1);
      u32 _369_11 = ((_entry_0 >> 14) & 1);
      u32 _369_12 = ((_entry_0 >> 15) & 1);
      u32 _369_13 = ((_entry_0 >> 16) & 1);
      u32 _369_14 = ((_entry_0 >> 17) & 1);
      u32 _369_15 = ((_entry_0 >> 18) & 1);
      u32 _369_16 = ((_entry_0 >> 19) & 1);
      u32 _369_17 = ((_entry_0 >> 20) & 1);
      u32 _369_18 = ((_entry_0 >> 21) & 1);
      u32 _369_19 = ((_entry_0 >> 22) & 1);
      u32 _369_20 = ((_entry_0 >> 23) & 1);
      u32 _369_21 = ((_entry_0 >> 24) & 1);
      u32 _369_22 = ((_entry_0 >> 25) & 1);
      u32 _369_23 = ((_entry_0 >> 26) & 1);
      u32 _369_24 = ((_entry_0 >> 27) & 1);
      u32 _369_25 = ((_entry_0 >> 28) & 1);
      u32 _369_26 = ((_entry_0 >> 29) & 1);
      u32 _369_27 = ((_entry_0 >> 30) & 1);
      u32 _369_28 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_37[1];
      if (spin_31(e, _o_37, term_ctr(CID_SCon, STAT_OFF + 450)) == 0) {
        return 0;
      }
      r0 = _o_37[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k421)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_2[1];
      if (spin_72(e, _o_2, _h_3) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_2[0];
      if (_v_0 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k422;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_go_k422, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k422, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_catalog_union_fast)) {
          u64 _t_3 = task_node(e, FID_catalog_union_fast, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_1;
          e.mem[_t_3 + 1] = _h_2;
          return term_tsk(FID_catalog_union_fast, _t_3);
        }
        r0 = _h_1;
        r1 = _h_2;
        WL_JMP(FID_catalog_union_fast);
      } else {
        term_sink(e, _h_1);
        term_sink(e, _h_2);
        Term _o_3[1];
        if (spin_31(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 190)) == 0) {
          return 0;
        }
        r0 = _o_3[0];
        WL_RETN(1);
      }
    } else {
      Term _o_4[1];
      if (spin_31(e, _o_4, term_ctr(CID_SCon, STAT_OFF + 302)) == 0) {
        return 0;
      }
      r0 = _o_4[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k422)
    Term _h_4 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_go_k423;
      WL_PUSHN(1);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_go_k423, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_go_k423, _t_4);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_catalog_union_ents)) {
      u64 _t_5 = task_node(e, FID_ffi_catalog_union_ents, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _h_4;
      return term_tsk(FID_ffi_catalog_union_ents, _t_5);
    }
    r0 = _h_4;
    WL_JMP(FID_ffi_catalog_union_ents);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k423)
    Term _h_5 = r0;
    WL_OPEN
    Term _rest_0 = term_pak(CID_SNil, 0);
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_0)) {
      u64 _t_6 = task_node(e, FID_wire_put_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_6 + 0] = _h_5;
      e.mem[_t_6 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_0, _t_6);
    }
    r0 = _h_5;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k424)
    u32 _h_6 = r0;
    Term _h_7 = r1;
    Term _h_8 = r2;
    WL_OPEN
    if (_h_6 == 0) {
      u32 _v_1 = 0;
      Term _o_6[1];
      if (spin_72(e, _o_6, _h_8) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_6[0];
      if (_v_1 == 1) {
        u32 _v_2 = 0;
        Term _v_3 = 0;
        Term _o_7[2];
        if (spin_70(e, _o_7, _h_7) == 0) {
          return 0;
        }
        _v_2 = (u32)_o_7[0];
        _v_3 = _o_7[1];
        if (_v_2 == 0) {
          Term _rest_1 = term_pak(CID_SNil, 0);
          Term _o_8[1];
          if (spin_8(e, _o_8, 0, _rest_1) == 0) {
            return 0;
          }
          r0 = _o_8[0];
          WL_RETN(1);
        } else {
          Term _rest_2 = term_pak(CID_SNil, 0);
          if (seq) {
            WL_ROOM(1, 0);
            STK(0) = FID_ffi_go_k425;
            WL_PUSHN(1);
          } else {
            u64 _t_9 = task_node(e, FID_ffi_go_k425, WL_CONT, WL_IDX, 1);
            WL_CONT = term_tsk(FID_ffi_go_k425, _t_9);
            WL_IDX = 0;
          }
          if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_0)) {
            u64 _t_10 = task_node(e, FID_wire_put_list_0, WL_CONT, WL_IDX, 0);
            e.mem[_t_10 + 0] = _v_3;
            e.mem[_t_10 + 1] = _rest_2;
            return term_tsk(FID_wire_put_list_0, _t_10);
          }
          r0 = _v_3;
          r1 = _rest_2;
          WL_JMP(FID_wire_put_list_0);
        }
      } else {
        term_sink(e, _h_7);
        Term _o_10[1];
        if (spin_31(e, _o_10, term_ctr(CID_SCon, STAT_OFF + 164)) == 0) {
          return 0;
        }
        r0 = _o_10[0];
        WL_RETN(1);
      }
    } else {
      Term _o_11[1];
      if (spin_31(e, _o_11, term_ctr(CID_SCon, STAT_OFF + 276)) == 0) {
        return 0;
      }
      r0 = _o_11[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k425)
    Term _h_9 = r0;
    WL_OPEN
    Term _o_9[1];
    if (spin_8(e, _o_9, 1ull, _h_9) == 0) {
      return 0;
    }
    r0 = _o_9[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k426)
    u32 _h_10 = r0;
    Term _h_11 = r1;
    Term _h_12 = r2;
    Term _h_13 = r3;
    Term _h_14 = r4;
    u32 _h_15 = r5;
    Term _h_16 = r6;
    WL_OPEN
    if (_h_10 == 0) {
      u32 _v_4 = 0;
      Term _o_13[1];
      if (spin_72(e, _o_13, _h_16) == 0) {
        return 0;
      }
      _v_4 = (u32)_o_13[0];
      if (_v_4 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k427;
          WL_PUSHN(1);
        } else {
          u64 _t_13 = task_node(e, FID_ffi_go_k427, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k427, _t_13);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_path_policy_judge)) {
          u64 _t_14 = task_node(e, FID_path_policy_judge, WL_CONT, WL_IDX, 0);
          e.mem[_t_14 + 0] = _h_11;
          e.mem[_t_14 + 1] = _h_12;
          e.mem[_t_14 + 2] = _h_13;
          e.mem[_t_14 + 3] = _h_14;
          e.mem[_t_14 + 4] = _h_15;
          return term_tsk(FID_path_policy_judge, _t_14);
        }
        r0 = _h_11;
        r1 = _h_12;
        r2 = _h_13;
        r3 = _h_14;
        r4 = _h_15;
        WL_JMP(FID_path_policy_judge);
      } else {
        term_sink(e, _h_11);
        term_sink(e, _h_12);
        term_sink(e, _h_13);
        term_sink(e, _h_14);
        Term _o_15[1];
        if (spin_31(e, _o_15, term_ctr(CID_SCon, STAT_OFF + 154)) == 0) {
          return 0;
        }
        r0 = _o_15[0];
        WL_RETN(1);
      }
    } else {
      Term _o_16[1];
      if (spin_31(e, _o_16, term_ctr(CID_SCon, STAT_OFF + 266)) == 0) {
        return 0;
      }
      r0 = _o_16[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k427)
    u32 _h_17 = r0;
    u32 _h_18 = r1;
    WL_OPEN
    Term _o_14[1];
    if (spin_69(e, _o_14, _h_17, _h_18, term_pak(CID_SNil, 0)) == 0) {
      return 0;
    }
    r0 = _o_14[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k428)
    u32 _h_19 = r0;
    Term _h_20 = r1;
    Term _h_21 = r2;
    WL_OPEN
    if (_h_19 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_20;
        STK(1) = FID_ffi_go_k429;
        WL_PUSHN(2);
      } else {
        u64 _t_17 = task_node(e, FID_ffi_go_k429, WL_CONT, WL_IDX, 1);
        e.mem[_t_17 + 0] = _h_20;
        WL_CONT = term_tsk(FID_ffi_go_k429, _t_17);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_u32)) {
        u64 _t_18 = task_node(e, FID_wire_get_u32, WL_CONT, WL_IDX, 0);
        e.mem[_t_18 + 0] = _h_21;
        return term_tsk(FID_wire_get_u32, _t_18);
      }
      r0 = _h_21;
      WL_JMP(FID_wire_get_u32);
    } else {
      Term _o_27[1];
      if (spin_30(e, _o_27) == 0) {
        return 0;
      }
      r0 = _o_27[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k429)
    WL_POPN(1);
    Term _h_25 = STK(0);
    u32 _h_22 = r0;
    u32 _h_23 = r1;
    Term _h_24 = r2;
    WL_OPEN
    if (_h_22 == 0) {
      u32 _v_5 = 0;
      u32 _v_6 = 0;
      Term _v_7 = 0;
      Term _o_18[3];
      if (spin_32(e, _o_18, _h_24) == 0) {
        return 0;
      }
      _v_5 = (u32)_o_18[0];
      _v_6 = (u32)_o_18[1];
      _v_7 = _o_18[2];
      if (_v_5 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _v_6;
          STK(1) = _h_25;
          STK(2) = _h_23;
          STK(3) = FID_ffi_go_k430;
          WL_PUSHN(4);
        } else {
          u64 _t_19 = task_node(e, FID_ffi_go_k430, WL_CONT, WL_IDX, 1);
          e.mem[_t_19 + 0] = _v_6;
          e.mem[_t_19 + 1] = _h_25;
          e.mem[_t_19 + 2] = _h_23;
          WL_CONT = term_tsk(FID_ffi_go_k430, _t_19);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
          u64 _t_20 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
          e.mem[_t_20 + 0] = _v_7;
          return term_tsk(FID_wire_get_str, _t_20);
        }
        r0 = _v_7;
        WL_JMP(FID_wire_get_str);
      } else {
        Term _o_25[1];
        if (spin_30(e, _o_25) == 0) {
          return 0;
        }
        r0 = _o_25[0];
        WL_RETN(1);
      }
    } else {
      Term _o_26[1];
      if (spin_30(e, _o_26) == 0) {
        return 0;
      }
      r0 = _o_26[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k430)
    WL_POPN(3);
    u32 _v_8 = STK(0);
    Term _h_29 = STK(1);
    u32 _h_30 = STK(2);
    u32 _h_26 = r0;
    Term _h_27 = r1;
    Term _h_28 = r2;
    WL_OPEN
    if (_h_26 == 0) {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _h_27;
        STK(1) = _h_29;
        STK(2) = _h_30;
        STK(3) = _v_8;
        STK(4) = FID_ffi_go_k431;
        WL_PUSHN(5);
      } else {
        u64 _t_21 = task_node(e, FID_ffi_go_k431, WL_CONT, WL_IDX, 1);
        e.mem[_t_21 + 0] = _h_27;
        e.mem[_t_21 + 1] = _h_29;
        e.mem[_t_21 + 2] = _h_30;
        e.mem[_t_21 + 3] = _v_8;
        WL_CONT = term_tsk(FID_ffi_go_k431, _t_21);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_0)) {
        u64 _t_22 = task_node(e, FID_wire_get_list_0, WL_CONT, WL_IDX, 0);
        e.mem[_t_22 + 0] = _h_28;
        return term_tsk(FID_wire_get_list_0, _t_22);
      }
      r0 = _h_28;
      WL_JMP(FID_wire_get_list_0);
    } else {
      Term _o_24[1];
      if (spin_30(e, _o_24) == 0) {
        return 0;
      }
      r0 = _o_24[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k431)
    WL_POPN(4);
    Term _h_34 = STK(0);
    Term _h_35 = STK(1);
    u32 _h_36 = STK(2);
    u32 _v_9 = STK(3);
    u32 _h_31 = r0;
    Term _h_32 = r1;
    Term _h_33 = r2;
    WL_OPEN
    if (_h_31 == 0) {
      if (term_aux(_h_33) == CID_SNil) {
        if (seq) {
          WL_ROOM(5, 0);
          STK(0) = _h_35;
          STK(1) = _h_36;
          STK(2) = _v_9;
          STK(3) = _h_34;
          STK(4) = FID_ffi_go_k432;
          WL_PUSHN(5);
        } else {
          u64 _t_23 = task_node(e, FID_ffi_go_k432, WL_CONT, WL_IDX, 1);
          e.mem[_t_23 + 0] = _h_35;
          e.mem[_t_23 + 1] = _h_36;
          e.mem[_t_23 + 2] = _v_9;
          e.mem[_t_23 + 3] = _h_34;
          WL_CONT = term_tsk(FID_ffi_go_k432, _t_23);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_0)) {
          u64 _t_24 = task_node(e, FID_wire_put_list_0, WL_CONT, WL_IDX, 0);
          e.mem[_t_24 + 0] = _h_32;
          e.mem[_t_24 + 1] = term_pak(CID_SNil, 0);
          return term_tsk(FID_wire_put_list_0, _t_24);
        }
        r0 = _h_32;
        r1 = term_pak(CID_SNil, 0);
        WL_JMP(FID_wire_put_list_0);
      } else {
        term_sink(e, _h_32);
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _h_33, 2, _fb_0);
        u32 _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        term_sink(e, _f_1);
        term_sink(e, _h_34);
        Term _o_22[1];
        if (spin_30(e, _o_22) == 0) {
          return 0;
        }
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _o_22[0];
        WL_RETN(1);
      }
    } else {
      term_sink(e, _h_34);
      Term _o_23[1];
      if (spin_30(e, _o_23) == 0) {
        return 0;
      }
      r0 = _o_23[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k432)
    WL_POPN(4);
    Term _h_38 = STK(0);
    u32 _h_39 = STK(1);
    u32 _v_10 = STK(2);
    Term _h_40 = STK(3);
    Term _h_37 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _h_38;
      STK(1) = _h_39;
      STK(2) = _v_10;
      STK(3) = FID_ffi_go_k433;
      WL_PUSHN(4);
    } else {
      u64 _t_25 = task_node(e, FID_ffi_go_k433, WL_CONT, WL_IDX, 1);
      e.mem[_t_25 + 0] = _h_38;
      e.mem[_t_25 + 1] = _h_39;
      e.mem[_t_25 + 2] = _v_10;
      WL_CONT = term_tsk(FID_ffi_go_k433, _t_25);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_str)) {
      u64 _t_26 = task_node(e, FID_wire_put_str, WL_CONT, WL_IDX, 0);
      e.mem[_t_26 + 0] = _h_40;
      e.mem[_t_26 + 1] = _h_37;
      return term_tsk(FID_wire_put_str, _t_26);
    }
    r0 = _h_40;
    r1 = _h_37;
    WL_JMP(FID_wire_put_str);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k433)
    WL_POPN(3);
    Term _h_42 = STK(0);
    u32 _h_43 = STK(1);
    u32 _v_11 = STK(2);
    Term _h_41 = r0;
    WL_OPEN
    Term _v_12 = 0;
    Term _v_13 = 0;
    Term _o_19[1];
    if (spin_28(e, _o_19, _v_11, _h_41) == 0) {
      return 0;
    }
    _v_13 = _o_19[0];
    Term _o_20[1];
    if (spin_29(e, _o_20, _h_43, _v_13) == 0) {
      return 0;
    }
    _v_12 = _o_20[0];
    Term _o_21[1];
    if (spin_8(e, _o_21, _h_42, _v_12) == 0) {
      return 0;
    }
    r0 = _o_21[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k434)
    u32 _h_44 = r0;
    Term _h_45 = r1;
    Term _h_46 = r2;
    WL_OPEN
    if (_h_44 == 0) {
      u32 _v_14 = 0;
      Term _o_29[1];
      if (spin_72(e, _o_29, _h_46) == 0) {
        return 0;
      }
      _v_14 = (u32)_o_29[0];
      if (_v_14 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k435;
          WL_PUSHN(1);
        } else {
          u64 _t_29 = task_node(e, FID_ffi_go_k435, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k435, _t_29);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_gateway_width_table)) {
          u64 _t_30 = task_node(e, FID_ffi_gateway_width_table, WL_CONT, WL_IDX, 0);
          e.mem[_t_30 + 0] = _h_45;
          return term_tsk(FID_ffi_gateway_width_table, _t_30);
        }
        r0 = _h_45;
        WL_JMP(FID_ffi_gateway_width_table);
      } else {
        term_sink(e, _h_45);
        Term _o_30[1];
        if (spin_31(e, _o_30, term_ctr(CID_SCon, STAT_OFF + 134)) == 0) {
          return 0;
        }
        r0 = _o_30[0];
        WL_RETN(1);
      }
    } else {
      Term _o_31[1];
      if (spin_31(e, _o_31, term_ctr(CID_SCon, STAT_OFF + 246)) == 0) {
        return 0;
      }
      r0 = _o_31[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k435)
    Term _h_47 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_go_k436;
      WL_PUSHN(1);
    } else {
      u64 _t_31 = task_node(e, FID_ffi_go_k436, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_go_k436, _t_31);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_gateway_width_layout)) {
      u64 _t_32 = task_node(e, FID_gateway_width_layout, WL_CONT, WL_IDX, 0);
      e.mem[_t_32 + 0] = _h_47;
      return term_tsk(FID_gateway_width_layout, _t_32);
    }
    r0 = _h_47;
    WL_JMP(FID_gateway_width_layout);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k436)
    Term _h_48 = r0;
    Term _h_49 = r1;
    WL_OPEN
    Term _rest_3 = term_pak(CID_SNil, 0);
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _h_48;
      STK(1) = _rest_3;
      STK(2) = FID_ffi_go_k437;
      WL_PUSHN(3);
    } else {
      u64 _t_33 = task_node(e, FID_ffi_go_k437, WL_CONT, WL_IDX, 1);
      e.mem[_t_33 + 0] = _h_48;
      e.mem[_t_33 + 1] = _rest_3;
      WL_CONT = term_tsk(FID_ffi_go_k437, _t_33);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_flat_flat)) {
      u64 _t_34 = task_node(e, FID_wire_flat_flat, WL_CONT, WL_IDX, 0);
      e.mem[_t_34 + 0] = _h_49;
      return term_tsk(FID_wire_flat_flat, _t_34);
    }
    r0 = _h_49;
    WL_JMP(FID_wire_flat_flat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k437)
    WL_POPN(2);
    Term _h_51 = STK(0);
    Term _rest_4 = STK(1);
    Term _h_50 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_51;
      STK(1) = FID_ffi_go_k438;
      WL_PUSHN(2);
    } else {
      u64 _t_35 = task_node(e, FID_ffi_go_k438, WL_CONT, WL_IDX, 1);
      e.mem[_t_35 + 0] = _h_51;
      WL_CONT = term_tsk(FID_ffi_go_k438, _t_35);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_gateway_width_put_ns)) {
      u64 _t_36 = task_node(e, FID_ffi_gateway_width_put_ns, WL_CONT, WL_IDX, 0);
      e.mem[_t_36 + 0] = _h_50;
      e.mem[_t_36 + 1] = _rest_4;
      return term_tsk(FID_ffi_gateway_width_put_ns, _t_36);
    }
    r0 = _h_50;
    r1 = _rest_4;
    WL_JMP(FID_ffi_gateway_width_put_ns);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k438)
    WL_POPN(1);
    Term _h_53 = STK(0);
    Term _h_52 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_ffi_gateway_width_put_ns)) {
      u64 _t_37 = task_node(e, FID_ffi_gateway_width_put_ns, WL_CONT, WL_IDX, 0);
      e.mem[_t_37 + 0] = _h_53;
      e.mem[_t_37 + 1] = _h_52;
      return term_tsk(FID_ffi_gateway_width_put_ns, _t_37);
    }
    r0 = _h_53;
    r1 = _h_52;
    WL_JMP(FID_ffi_gateway_width_put_ns);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k439)
    u32 _h_54 = r0;
    Term _h_55 = r1;
    Term _h_56 = r2;
    Term _h_57 = r3;
    WL_OPEN
    if (_h_54 == 0) {
      u32 _v_15 = 0;
      Term _o_33[1];
      if (spin_72(e, _o_33, _h_57) == 0) {
        return 0;
      }
      _v_15 = (u32)_o_33[0];
      if (_v_15 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k440;
          WL_PUSHN(1);
        } else {
          u64 _t_40 = task_node(e, FID_ffi_go_k440, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k440, _t_40);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_tiny_pick)) {
          u64 _t_41 = task_node(e, FID_tiny_pick, WL_CONT, WL_IDX, 0);
          e.mem[_t_41 + 0] = _h_55;
          e.mem[_t_41 + 1] = _h_56;
          return term_tsk(FID_tiny_pick, _t_41);
        }
        r0 = _h_55;
        r1 = _h_56;
        WL_JMP(FID_tiny_pick);
      } else {
        term_sink(e, _h_55);
        term_sink(e, _h_56);
        Term _o_35[1];
        if (spin_31(e, _o_35, term_ctr(CID_SCon, STAT_OFF + 108)) == 0) {
          return 0;
        }
        r0 = _o_35[0];
        WL_RETN(1);
      }
    } else {
      Term _o_36[1];
      if (spin_31(e, _o_36, term_ctr(CID_SCon, STAT_OFF + 220)) == 0) {
        return 0;
      }
      r0 = _o_36[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k440)
    u32 _h_58 = r0;
    Term _h_59 = r1;
    WL_OPEN
    Term _o_34[1];
    if (spin_66(e, _o_34, _h_58, _h_59, term_pak(CID_SNil, 0)) == 0) {
      return 0;
    }
    r0 = _o_34[0];
    WL_RETN(1);
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
        STK(0) = FID_open_go_k444;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_open_go_k444, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_open_go_k444, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_echo_open)) {
        u64 _t_1 = task_node(e, FID_ffi_echo_open, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_ffi_echo_open, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_echo_open);
    } else {
      u32 _9_0 = ((_entry_0 >> 0) & 1);
      u32 _10_0 = ((_entry_0 >> 1) & 1);
      u32 _10_1 = ((_entry_0 >> 2) & 1);
      u32 _10_2 = ((_entry_0 >> 3) & 1);
      u32 _10_3 = ((_entry_0 >> 4) & 1);
      u32 _10_4 = ((_entry_0 >> 5) & 1);
      u32 _10_5 = ((_entry_0 >> 6) & 1);
      u32 _10_6 = ((_entry_0 >> 7) & 1);
      u32 _10_7 = ((_entry_0 >> 8) & 1);
      u32 _10_8 = ((_entry_0 >> 9) & 1);
      u32 _10_9 = ((_entry_0 >> 10) & 1);
      u32 _10_10 = ((_entry_0 >> 11) & 1);
      u32 _10_11 = ((_entry_0 >> 12) & 1);
      u32 _10_12 = ((_entry_0 >> 13) & 1);
      u32 _10_13 = ((_entry_0 >> 14) & 1);
      u32 _10_14 = ((_entry_0 >> 15) & 1);
      u32 _10_15 = ((_entry_0 >> 16) & 1);
      u32 _10_16 = ((_entry_0 >> 17) & 1);
      u32 _10_17 = ((_entry_0 >> 18) & 1);
      u32 _10_18 = ((_entry_0 >> 19) & 1);
      u32 _10_19 = ((_entry_0 >> 20) & 1);
      u32 _10_20 = ((_entry_0 >> 21) & 1);
      u32 _10_21 = ((_entry_0 >> 22) & 1);
      u32 _10_22 = ((_entry_0 >> 23) & 1);
      u32 _10_23 = ((_entry_0 >> 24) & 1);
      u32 _10_24 = ((_entry_0 >> 25) & 1);
      u32 _10_25 = ((_entry_0 >> 26) & 1);
      u32 _10_26 = ((_entry_0 >> 27) & 1);
      u32 _10_27 = ((_entry_0 >> 28) & 1);
      u32 _10_28 = ((_entry_0 >> 29) & 1);
      u32 _10_29 = ((_entry_0 >> 30) & 1);
      u32 _10_30 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = term_ctr(CID_SCon, STAT_OFF + 454);
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_go_k444)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_75(e, _o_0, _h_0, _h_1, _h_2, _h_3) == 0) {
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
  WL_CASE(FID_step)
    u32 _state_0 = r0;
    u32 _state_1 = r1;
    Term _state_2 = r2;
    Term _state_3 = r3;
    Term _input_0 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_step_k446;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_step_k446, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_step_k446, _t_0);
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
  WL_CASE(FID_step_k446)
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
    if (spin_76(e, _o_0, _state_0, _state_1, _state_2, _state_3) == 0) {
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
      STK(0) = FID_ffi_k450;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_k450, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_k450, _t_0);
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
  WL_CASE(FID_ffi_k450)
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
      STK(0) = FID_open_k455;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_open_k455, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_open_k455, _t_0);
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
  WL_CASE(FID_open_k455)
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
        STK(1) = FID_cli_steps_k457;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_cli_steps_k457, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _r_4;
        WL_CONT = term_tsk(FID_cli_steps_k457, _t_0);
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
        STK(2) = FID_cli_steps_k458;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_cli_steps_k458, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _f_1;
        e.mem[_t_2 + 1] = _r_4;
        WL_CONT = term_tsk(FID_cli_steps_k458, _t_2);
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
  WL_CASE(FID_cli_steps_k457)
    WL_POPN(1);
    Term _r_5 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_78(e, _o_0, _r_5) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k458)
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
      STK(1) = FID_cli_steps_k459;
      WL_PUSHN(2);
    } else {
      u64 _t_4 = task_node(e, FID_cli_steps_k459, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _r_6;
      WL_CONT = term_tsk(FID_cli_steps_k459, _t_4);
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
  WL_CASE(FID_cli_steps_k459)
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
      r0 = term_clo(FID_cli_print_c471, 0);
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
      r0 = term_clo(FID_cli_print_c472, _nd_0);
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c471)
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
  WL_CASE(FID_cli_print_c472)
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
      e.mem[_t_2 + 1] = term_clo(FID_cli_print_c473, _nd_2);
      e.mem[_t_2 + 2] = _x_2;
      return term_tsk(FID_IO_bind, _t_2);
    }
    r0 = term_clo(FID_IO_print, _nd_1);
    r1 = term_clo(FID_cli_print_c473, _nd_2);
    r2 = _x_2;
    WL_JMP(FID_IO_bind);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c473)
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
              STK(3) = FID_cli_args_k475;
              WL_PUSHN(4);
            } else {
              u64 _t_0 = task_node(e, FID_cli_args_k475, WL_CONT, WL_IDX, 1);
              e.mem[_t_0 + 0] = _f_2;
              e.mem[_t_0 + 1] = _f_6;
              e.mem[_t_0 + 2] = _f_7;
              WL_CONT = term_tsk(FID_cli_args_k475, _t_0);
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
  WL_CASE(FID_cli_args_k475)
    WL_POPN(3);
    Term _f_8 = STK(0);
    Term _f_9 = STK(1);
    Term _f_10 = STK(2);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_2[1];
    if (spin_80(e, _o_2, _f_8, term_ctr(CID_SCon, STAT_OFF + 462)) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_2[0];
    u32 _v_2 = 0;
    Term _o_3[1];
    if (spin_80(e, _o_3, _f_8, term_ctr(CID_SCon, STAT_OFF + 470)) == 0) {
      return 0;
    }
    term_sink(e, _f_8);
    _v_2 = (u32)_o_3[0];
    if (_v_0 == 1) {
      if (_v_2 == 0) {
        if (_h_0 == 1) {
          if (term_aux(_f_10) == CID_Nil) {
            if (seq) {
              WL_ROOM(1, 0);
              STK(0) = FID_cli_args_k476;
              WL_PUSHN(1);
            } else {
              u64 _t_2 = task_node(e, FID_cli_args_k476, WL_CONT, WL_IDX, 1);
              WL_CONT = term_tsk(FID_cli_args_k476, _t_2);
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
      if (_v_2 == 1) {
        if (_h_0 == 1) {
          if (seq) {
            WL_ROOM(2, 0);
            STK(0) = _f_10;
            STK(1) = FID_cli_args_k477;
            WL_PUSHN(2);
          } else {
            u64 _t_4 = task_node(e, FID_cli_args_k477, WL_CONT, WL_IDX, 1);
            e.mem[_t_4 + 0] = _f_10;
            WL_CONT = term_tsk(FID_cli_args_k477, _t_4);
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
  WL_CASE(FID_cli_args_k476)
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
  WL_CASE(FID_cli_args_k477)
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
      STK(0) = FID_cli_args_k478;
      WL_PUSHN(1);
    } else {
      u64 _t_6 = task_node(e, FID_cli_args_k478, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_cli_args_k478, _t_6);
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
  WL_CASE(FID_cli_args_k478)
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
      e.mem[_t_3 + 1] = term_clo(FID_IO_bind_c482, _nd_0);
      return term_tsk(FID_Clo_apply, _t_3);
    }
    r0 = _m_0;
    r1 = term_clo(FID_IO_bind_c482, _nd_0);
    WL_JMP(FID_Clo_apply);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_bind_c482)
    Term _f_1 = r0;
    Term _k_1 = r1;
    Term _x_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _k_1;
      STK(1) = FID_IO_bind_k483;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_IO_bind_k483, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _k_1;
      WL_CONT = term_tsk(FID_IO_bind_k483, _t_0);
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
  WL_CASE(FID_IO_bind_k483)
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
    r0 = term_clo(FID_main_c485, 0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c485)
    Term _x_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_IO_bind)) {
      u64 _t_3 = task_node(e, FID_IO_bind, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = term_clo(FID_IO_args, 0);
      e.mem[_t_3 + 1] = term_clo(FID_main_c486, 0);
      e.mem[_t_3 + 2] = _x_0;
      return term_tsk(FID_IO_bind, _t_3);
    }
    r0 = term_clo(FID_IO_args, 0);
    r1 = term_clo(FID_main_c486, 0);
    r2 = _x_0;
    WL_JMP(FID_IO_bind);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c486)
    Term _x_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_main_k487;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_main_k487, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_main_k487, _t_0);
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
  WL_CASE(FID_main_k487)
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
      r0 = term_clo(FID_main_c488, 0);
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c488)
    Term _x_2 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_81(e, _o_0, 2ull, term_ctr(CID_SCon, STAT_OFF + 616), _x_2) == 0) {
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
