
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
#define CID_Admission 20
#define CID_Unknown 21
#define CID_LT 22
#define CID_EQ 23
#define CID_GT 24
#define CID_ffi_echo_Echo 25
#define CID_ffi_echo_Refused 26
#define CID_ffi_admission_Running 27
#define CID_ffi_admission_Shut 28
#define CID_admission_Live 29
#define CID_WNil 30
#define CID_admission_Unl 31
#define CID_admission_Cap 32
#define CID_admission_Lv 33
#define CID_wire_Got 34
#define CID_wire_Bad 35
#define CID_admission_Ia 36
#define CID_admission_Bg 37
#define CID_admission_Queued 38
#define CID_admission_Granted 39
#define CID_admission_Held 40
#define CID_admission_Preempted 41
#define CID_admission_Ended 42
#define CID_doc_lines_Run 43
#define CID_default_model_In 44
#define CID_ffi_aux_fallback_GateReq 45
#define CID_ffi_aux_fallback_SettleReq 46
#define CID_ffi_aux_fallback_PassReq 47
#define CID_ffi_workflow_AdmitReq 48
#define CID_ffi_workflow_LimitsReq 49
#define CID_doc_seen_Iv 50
#define CID_admission_Admit 51
#define CID_admission_Collect 52
#define CID_admission_Release 53
#define CID_admission_Leave 54
#define CID_admission_Limit 55
#define CID_wire_Dig 56
#define CID_wire_Comma 57
#define CID_wire_Other 58
#define CID_ffi_child_T0 59
#define CID_ffi_child_T1 60
#define CID_ffi_child_T2 61
#define CID_ffi_child_T3 62
#define CID_ffi_child_T4 63
#define CID_ffi_child_TBad 64
#define CID_doc_lines_Lf 65
#define CID_doc_lines_CrLf 66
#define CID_default_model_NoDefault 67
#define CID_default_model_Default 68
#define CID_default_model_NoNext 69
#define CID_default_model_Next 70
#define CID_aux_fallback_Unset 71
#define CID_aux_fallback_Same 72
#define CID_aux_fallback_Other 73
#define CID_aux_fallback_Known 74
#define CID_aux_fallback_Lookup 75
#define CID_aux_fallback_Miss 76
#define CID_aux_fallback_Hit 77
#define CID_aux_fallback_Session 78
#define CID_aux_fallback_Routed 79
#define CID_aux_fallback_Fallback 80
#define CID_aux_fallback_K 81
#define CID_workflow_Queued 82
#define CID_workflow_Running 83
#define CID_workflow_Finished 84
#define CID_workflow_Erred 85
#define CID_workflow_Cancelled 86
#define CID_workflow_Cached 87
#define CID_workflow_Row 88
#define CID_workflow_Pool 89
#define CID_doc_seen_At 90
#define CID_job_Live 91
#define CID_job_Ended 92
#define CID_child_Cfg 93
#define CID_child_Queued 94
#define CID_child_Withdrawn 95
#define CID_child_Placed 96
#define CID_child_Watching 97
#define CID_child_Owing 98
#define CID_child_Ended 99
#define CID_progress_Prior 100
#define CID_default_model_Runs 101
#define CID_default_model_Nothing 102
#define CID_default_model_Refused 103
#define CID_job_Exited 104
#define CID_job_Killed 105
#define CID_job_Out 106
#define CID_job_Quit 107
#define CID_job_Kill 108
#define CID_job_Tick 109
#define CID_child_W 110
#define CID_child_Completed 111
#define CID_child_Failed 112
#define CID_child_Cancelled 113
#define CID_child_Stalled 114
#define CID_child_Unreachable 115
#define CID_doc_lines_Seps 116
#define CID_default_model_Saved 117
#define CID_default_model_Other 118
#define CID_default_model_Kept 119
#define CID_default_model_Swapped 120
#define CID_default_model_K 121
#define CID_aux_fallback_Stay 122
#define CID_aux_fallback_Went 123
#define CID_aux_fallback_Sub 124
#define CID_aux_fallback_Note 125
#define CID_workflow_Ended 126
#define CID_workflow_Reattach 127
#define CID_workflow_Reuse 128
#define CID_workflow_Spawn 129
#define CID_workflow_Refused 130
#define CID_workflow_Limits 131
#define CID_doc_seen_Check 132
#define CID_job_Code 133
#define CID_sandbox_Keep 134
#define CID_sandbox_Clash 135
#define CID_sandbox_Take 136
#define CID_sandbox_Drop 137
#define CID_default_model_NotInCatalog 138
#define CID_default_model_NoCredentials 139
#define CID_default_model_NotInScope 140
#define CID_doc_seen_Show 141
#define CID_admission_Holding 142
#define CID_admission_Waiting 143
#define CID_child_Busy 144
#define CID_child_Lost 145
#define CID_child_Answered 146
#define CID_child_Broke 147
#define CID_child_Gone 148
#define CID_child_Submit 149
#define CID_child_Await 150
#define CID_child_Resubmit 151
#define CID_child_Delivered 152
#define CID_progress_Go 153
#define CID_progress_Stop 154
#define CID_child_Inbox 155
#define CID_child_Silent 156
#define CID_admission_Tk 157
#define CID_child_Watches 158
#define CID_child_Reports 159
#define CID_child_Settles 160
#define CID_child_Watch 161
#define CID_child_Owe 162
#define CID_child_Quiet 163
#define CID_IO_args 164
#define CID_IO_print 165
#define FID_ffi_workflow_get_row 0
#define FID_ffi_workflow_get_row_k50 1
#define FID_ffi_workflow_get_row_k51 2
#define FID_wire_get_list_go_7 3
#define FID_wire_get_list_go_7_k53 4
#define FID_wire_get_list_go_7_k54 5
#define FID_ffi_job_get_end 6
#define FID_ffi_job_get_end_k77 7
#define FID_ffi_job_get_end_k78 8
#define FID_wire_put_list_go_9 9
#define FID_wire_put_list_go_9_k84 10
#define FID_doc_seen_fits 11
#define FID_doc_seen_fits_k95 12
#define FID_ffi_workflow_get_sts 13
#define FID_ffi_workflow_get_sts_k100 14
#define FID_ffi_workflow_get_pool 15
#define FID_ffi_workflow_get_pool_k105 16
#define FID_ffi_workflow_get_pool_k106 17
#define FID_ffi_aux_fallback_get_key 18
#define FID_ffi_aux_fallback_get_key_k111 19
#define FID_ffi_aux_fallback_get_key_k112 20
#define FID_ffi_aux_fallback_get_key_k113 21
#define FID_wire_get_list_go_1 22
#define FID_wire_get_list_go_1_k115 23
#define FID_wire_get_list_go_1_k116 24
#define FID_wire_get_list_go_6 25
#define FID_wire_get_list_go_6_k132 26
#define FID_wire_get_list_go_6_k133 27
#define FID_wire_put_str_go 28
#define FID_wire_put_str_go_k135 29
#define FID_ffi_child_get_mode 30
#define FID_ffi_child_get_mode_k151 31
#define FID_ffi_job_get_code 32
#define FID_ffi_job_get_code_k157 33
#define FID_ffi_job_get_code_k158 34
#define FID_wire_put_list_9 35
#define FID_wire_put_list_9_k164 36
#define FID_admission_lv_mark 37
#define FID_admission_lv_mark_k170 38
#define FID_ffi_doc_seen_get_mnat 39
#define FID_ffi_doc_seen_get_mnat_k177 40
#define FID_ffi_doc_seen_get_mnat_k178 41
#define FID_List_length 42
#define FID_List_length_k184 43
#define FID_doc_seen_whole_go 44
#define FID_List_take 45
#define FID_List_take_k188 46
#define FID_doc_seen_shows 47
#define FID_doc_seen_shows_k190 48
#define FID_doc_seen_lines 49
#define FID_doc_seen_lines_k192 50
#define FID_wire_put_list_go_6 51
#define FID_wire_put_list_go_6_k194 52
#define FID_wire_put_list_go_5 53
#define FID_wire_put_list_go_5_k196 54
#define FID_wire_get_list_7 55
#define FID_wire_get_list_7_k201 56
#define FID_wire_get_list_7_k202 57
#define FID_wire_put_list_go_1 58
#define FID_wire_put_list_go_1_k227 59
#define FID_wire_put_list_go_2 60
#define FID_wire_put_list_go_2_k229 61
#define FID_ffi_default_model_get_next 62
#define FID_ffi_default_model_get_next_k233 63
#define FID_ffi_default_model_get_next_k234 64
#define FID_wire_take 65
#define FID_wire_take_k244 66
#define FID_wire_put_str 67
#define FID_wire_put_str_k248 68
#define FID_ffi_child_get_report 69
#define FID_ffi_child_get_report_k255 70
#define FID_ffi_child_get_fate 71
#define FID_ffi_child_get_fate_k262 72
#define FID_ffi_child_get_obs 73
#define FID_ffi_child_get_obs_k271 74
#define FID_ffi_child_get_obs_k272 75
#define FID_wire_put_list_go_0 76
#define FID_wire_put_list_go_0_k290 77
#define FID_admission_lv_pick 78
#define FID_admission_lv_pick_k292 79
#define FID_admission_lv_pick_k293 80
#define FID_admission_lv_pick_k294 81
#define FID_admission_lv_pick_k295 82
#define FID_admission_lv_waits 83
#define FID_admission_lv_waits_k297 84
#define FID_admission_lv_waits_k298 85
#define FID_admission_lv_grant_go 86
#define FID_admission_lv_grant_go_k300 87
#define FID_admission_lv_grant_go_k301 88
#define FID_admission_lv_drop 89
#define FID_admission_lv_drop_k303 90
#define FID_admission_lv_set 91
#define FID_admission_lv_set_k306 92
#define FID_admission_lv_held 93
#define FID_admission_lv_held_k308 94
#define FID_admission_lv_held_k309 95
#define FID_admission_lv_cnt 96
#define FID_admission_lv_cnt_k314 97
#define FID_admission_lv_preempt 98
#define FID_admission_lv_preempt_k320 99
#define FID_List_append 100
#define FID_List_append_k322 101
#define FID_doc_seen_unseen 102
#define FID_doc_seen_unseen_k327 103
#define FID_wire_put_list_6 104
#define FID_wire_put_list_6_k336 105
#define FID_wire_put_list_5 106
#define FID_wire_put_list_5_k338 107
#define FID_workflow_found 108
#define FID_workflow_found_k349 109
#define FID_wire_get_list_1 110
#define FID_wire_get_list_1_k357 111
#define FID_wire_get_list_1_k358 112
#define FID_ffi_aux_fallback_get_look 113
#define FID_ffi_aux_fallback_get_look_k365 114
#define FID_ffi_aux_fallback_get_look_k366 115
#define FID_ffi_aux_fallback_get_look_k367 116
#define FID_ffi_aux_fallback_get_sel 117
#define FID_ffi_aux_fallback_get_sel_k371 118
#define FID_ffi_aux_fallback_get_sel_k372 119
#define FID_aux_fallback_listed 120
#define FID_aux_fallback_listed_k376 121
#define FID_wire_put_list_1 122
#define FID_wire_put_list_1_k379 123
#define FID_wire_get_list_6 124
#define FID_wire_get_list_6_k401 125
#define FID_wire_get_list_6_k402 126
#define FID_wire_put_list_go_4 127
#define FID_wire_put_list_go_4_k413 128
#define FID_ffi_child_get_maybe_nat 129
#define FID_ffi_child_get_maybe_nat_k425 130
#define FID_ffi_child_get_maybe_nat_k426 131
#define FID_wire_value 132
#define FID_wire_value_k436 133
#define FID_ffi_admission_get_cls 134
#define FID_ffi_admission_get_cls_k455 135
#define FID_wire_put_list_0 136
#define FID_wire_put_list_0_k458 137
#define FID_admission_lv_grant 138
#define FID_admission_lv_grant_k461 139
#define FID_admission_lv_grant_k462 140
#define FID_admission_lv_leave 141
#define FID_admission_lv_leave_k464 142
#define FID_admission_lv_leave_k465 143
#define FID_admission_lv_release 144
#define FID_admission_lv_release_k467 145
#define FID_admission_lv_find 146
#define FID_admission_lv_find_k469 147
#define FID_admission_lv_collect 148
#define FID_admission_lv_admit_bg 149
#define FID_admission_lv_admit_bg_k472 150
#define FID_admission_lv_admit_bg_k473 151
#define FID_admission_lv_admit_bg_k474 152
#define FID_admission_lv_admit_bg_k475 153
#define FID_admission_lv_admit_ia 154
#define FID_admission_lv_admit_ia_k477 155
#define FID_admission_lv_admit_ia_k478 156
#define FID_admission_lv_admit_ia_k479 157
#define FID_admission_lv_admit_ia_k480 158
#define FID_ffi_doc_seen_get_at 159
#define FID_ffi_doc_seen_get_at_k484 160
#define FID_ffi_doc_seen_get_at_k485 161
#define FID_wire_get_list_go_4 162
#define FID_wire_get_list_go_4_k487 163
#define FID_wire_get_list_go_4_k488 164
#define FID_doc_seen_check 165
#define FID_doc_seen_check_k490 166
#define FID_doc_seen_check_k491 167
#define FID_doc_seen_check_k492 168
#define FID_doc_seen_check_k493 169
#define FID_doc_seen_check_k494 170
#define FID_doc_seen_check_k495 171
#define FID_ffi_workflow_get_prior 172
#define FID_ffi_workflow_get_prior_k502 173
#define FID_ffi_workflow_get_prior_k503 174
#define FID_workflow_admit 175
#define FID_workflow_admit_k511 176
#define FID_ffi_aux_fallback_get_route 177
#define FID_ffi_aux_fallback_get_route_k514 178
#define FID_ffi_aux_fallback_get_route_k515 179
#define FID_ffi_aux_fallback_get_gate 180
#define FID_ffi_aux_fallback_get_gate_k519 181
#define FID_ffi_aux_fallback_get_gate_k520 182
#define FID_ffi_aux_fallback_get_gate_k521 183
#define FID_ffi_aux_fallback_get_gate_k522 184
#define FID_aux_fallback_after 185
#define FID_aux_fallback_after_k529 186
#define FID_aux_fallback_put 187
#define FID_aux_fallback_put_k531 188
#define FID_wire_get_str 189
#define FID_wire_get_str_k557 190
#define FID_ffi_doc_lines_get_mend 191
#define FID_ffi_doc_lines_get_mend_k565 192
#define FID_ffi_doc_lines_get_mend_k566 193
#define FID_doc_lines_plan 194
#define FID_doc_lines_plan_k571 195
#define FID_ffi_child_get_w 196
#define FID_ffi_child_get_w_k585 197
#define FID_ffi_child_get_w_k586 198
#define FID_ffi_child_get_w_k587 199
#define FID_wire_cdig_go 200
#define FID_wire_cdig_go_k594 201
#define FID_wire_get_nat_go 202
#define FID_wire_get_nat_go_k597 203
#define FID_wire_get_nat_go_k598 204
#define FID_wire_get_nat_end 205
#define FID_wire_get_nat_end_k600 206
#define FID_ffi_job_get_ev 207
#define FID_ffi_job_get_ev_k610 208
#define FID_ffi_job_get_ev_k611 209
#define FID_ffi_job_get_ev_k612 210
#define FID_U32_show_go 211
#define FID_ffi_admission_put_live 212
#define FID_ffi_admission_put_live_k627 213
#define FID_admission_Live_step 214
#define FID_admission_Live_step_k629 215
#define FID_admission_Live_step_k630 216
#define FID_admission_Live_step_k631 217
#define FID_admission_Live_step_k632 218
#define FID_admission_Live_step_k633 219
#define FID_admission_Live_step_k634 220
#define FID_admission_Live_step_k635 221
#define FID_admission_Live_step_k636 222
#define FID_admission_Live_step_k637 223
#define FID_ffi_doc_seen_get_iv 224
#define FID_ffi_doc_seen_get_iv_k640 225
#define FID_ffi_doc_seen_get_iv_k641 226
#define FID_wire_get_list_go_5 227
#define FID_wire_get_list_go_5_k643 228
#define FID_wire_get_list_go_5_k644 229
#define FID_ffi_progress_get_prior 230
#define FID_ffi_progress_get_prior_k680 231
#define FID_ffi_progress_get_prior_k681 232
#define FID_ffi_progress_get_prior_k682 233
#define FID_ffi_doc_lines_get_run 234
#define FID_ffi_doc_lines_get_run_k696 235
#define FID_ffi_doc_lines_get_run_k697 236
#define FID_wire_get_list_go_3 237
#define FID_wire_get_list_go_3_k699 238
#define FID_wire_get_list_go_3_k700 239
#define FID_ffi_child_get_ph 240
#define FID_ffi_child_get_ph_k706 241
#define FID_ffi_child_get_ph_k707 242
#define FID_ffi_child_get_ph_k708 243
#define FID_ffi_child_get_ph_k709 244
#define FID_ffi_child_get_mfate 245
#define FID_ffi_child_get_mfate_k712 246
#define FID_ffi_child_get_mfate_k713 247
#define FID_ffi_child_get_cfg 248
#define FID_ffi_child_get_cfg_k717 249
#define FID_ffi_child_get_cfg_k718 250
#define FID_wire_tok 251
#define FID_wire_tok_k725 252
#define FID_ffi_job_get_job 253
#define FID_ffi_job_get_job_k730 254
#define FID_ffi_job_get_job_k731 255
#define FID_ffi_job_get_job_k732 256
#define FID_ffi_job_get_job_k733 257
#define FID_ffi_job_get_job_k734 258
#define FID_ffi_job_get_job_k735 259
#define FID_Nat_show_fin 260
#define FID_wire_get_list_4 261
#define FID_wire_get_list_4_k761 262
#define FID_wire_get_list_4_k762 263
#define FID_ffi_default_model_get_saved 264
#define FID_ffi_default_model_get_saved_k790 265
#define FID_ffi_default_model_get_saved_k791 266
#define FID_wire_get_u32 267
#define FID_wire_get_u32_k800 268
#define FID_ffi_doc_lines_get_end 269
#define FID_ffi_doc_lines_get_end_k813 270
#define FID_wire_peek 271
#define FID_wire_peek_k828 272
#define FID_ffi_job_get_cap 273
#define FID_ffi_job_get_cap_k832 274
#define FID_ffi_job_get_cap_k833 275
#define FID_ffi_admission_get_lim 276
#define FID_ffi_admission_get_lim_k839 277
#define FID_ffi_admission_get_lim_k840 278
#define FID_U32_show 279
#define FID_ffi_admission_get_op 280
#define FID_ffi_admission_get_op_k848 281
#define FID_ffi_admission_get_op_k849 282
#define FID_ffi_admission_get_op_k850 283
#define FID_ffi_admission_get_op_k851 284
#define FID_ffi_admission_get_op_k852 285
#define FID_ffi_admission_get_op_k853 286
#define FID_ffi_admission_get_op_k854 287
#define FID_Nat_show 288
#define FID_String_append 289
#define FID_String_append_k860 290
#define FID_wire_get_list_5 291
#define FID_wire_get_list_5_k862 292
#define FID_wire_get_list_5_k863 293
#define FID_ffi_workflow_get_req 294
#define FID_ffi_workflow_get_req_k869 295
#define FID_ffi_workflow_get_req_k870 296
#define FID_ffi_workflow_get_req_k871 297
#define FID_ffi_workflow_get_req_k872 298
#define FID_ffi_workflow_get_req_k873 299
#define FID_ffi_workflow_get_req_k874 300
#define FID_ffi_workflow_get_req_k875 301
#define FID_ffi_workflow_get_req_k876 302
#define FID_ffi_aux_fallback_get_req 303
#define FID_ffi_aux_fallback_get_req_k880 304
#define FID_ffi_aux_fallback_get_req_k881 305
#define FID_ffi_aux_fallback_get_req_k882 306
#define FID_ffi_aux_fallback_get_req_k883 307
#define FID_ffi_aux_fallback_get_req_k884 308
#define FID_ffi_aux_fallback_get_req_k885 309
#define FID_ffi_aux_fallback_get_req_k886 310
#define FID_ffi_aux_fallback_get_req_k887 311
#define FID_ffi_default_model_get_in 312
#define FID_ffi_default_model_get_in_k894 313
#define FID_ffi_default_model_get_in_k895 314
#define FID_ffi_sandbox_get_doc 315
#define FID_ffi_sandbox_get_doc_k908 316
#define FID_ffi_sandbox_get_doc_k909 317
#define FID_wire_get_list_3 318
#define FID_wire_get_list_3_k914 319
#define FID_wire_get_list_3_k915 320
#define FID_wire_get_nat 321
#define FID_wire_get_nat_k930 322
#define FID_wire_get_nat_k931 323
#define FID_ffi_admission_get_open 324
#define FID_ffi_admission_get_open_k938 325
#define FID_ffi_admission_get_open_k939 326
#define FID_ffi_admission_step 327
#define FID_ffi_admission_step_k945 328
#define FID_ffi_admission_step_k946 329
#define FID_ffi_admission_step_k947 330
#define FID_ffi_echo_step 331
#define FID_ffi_echo_step_k950 332
#define FID_ffi_echo_step_k951 333
#define FID_ffi_echo_step_k952 334
#define FID_ffi_admission_open 335
#define FID_ffi_admission_open_k1009 336
#define FID_ffi_admission_open_k1010 337
#define FID_ffi_echo_open 338
#define FID_ffi_echo_open_k1014 339
#define FID_ffi_echo_open_k1015 340
#define FID_step_go 341
#define FID_step_go_k1018 342
#define FID_step_go_k1019 343
#define FID_ffi_go 344
#define FID_ffi_go_k1022 345
#define FID_ffi_go_k1023 346
#define FID_ffi_go_k1024 347
#define FID_ffi_go_k1025 348
#define FID_ffi_go_k1026 349
#define FID_ffi_go_k1027 350
#define FID_ffi_go_k1028 351
#define FID_ffi_go_k1029 352
#define FID_ffi_go_k1030 353
#define FID_ffi_go_k1031 354
#define FID_ffi_go_k1032 355
#define FID_ffi_go_k1033 356
#define FID_ffi_go_k1034 357
#define FID_ffi_go_k1035 358
#define FID_ffi_go_k1036 359
#define FID_ffi_go_k1037 360
#define FID_ffi_go_k1038 361
#define FID_ffi_go_k1039 362
#define FID_ffi_go_k1040 363
#define FID_ffi_go_k1041 364
#define FID_ffi_go_k1042 365
#define FID_ffi_go_k1043 366
#define FID_ffi_go_k1044 367
#define FID_ffi_go_k1045 368
#define FID_ffi_go_k1046 369
#define FID_ffi_go_k1047 370
#define FID_ffi_go_k1048 371
#define FID_ffi_go_k1049 372
#define FID_ffi_go_k1050 373
#define FID_ffi_go_k1051 374
#define FID_ffi_go_k1052 375
#define FID_ffi_go_k1053 376
#define FID_ffi_go_k1054 377
#define FID_ffi_go_k1055 378
#define FID_ffi_go_k1056 379
#define FID_ffi_go_k1057 380
#define FID_ffi_go_k1058 381
#define FID_ffi_go_k1059 382
#define FID_ffi_go_k1060 383
#define FID_ffi_go_k1061 384
#define FID_ffi_go_k1062 385
#define FID_ffi_go_k1063 386
#define FID_ffi_go_k1064 387
#define FID_open_go 388
#define FID_open_go_k1068 389
#define FID_open_go_k1069 390
#define FID_step 391
#define FID_step_k1071 392
#define FID_close 393
#define FID_ffi 394
#define FID_ffi_k1075 395
#define FID_U32_read_go 396
#define FID_open 397
#define FID_open_k1080 398
#define FID_cli_steps 399
#define FID_cli_steps_k1082 400
#define FID_cli_steps_k1083 401
#define FID_cli_steps_k1084 402
#define FID_U32_read 403
#define FID_cli_print 404
#define FID_cli_print_c1096 405
#define FID_cli_print_c1097 406
#define FID_cli_print_c1098 407
#define FID_cli_args 408
#define FID_cli_args_k1100 409
#define FID_cli_args_k1101 410
#define FID_cli_args_k1102 411
#define FID_cli_args_k1103 412
#define FID_IO_bind 413
#define FID_IO_bind_c1107 414
#define FID_IO_bind_k1108 415
#define FID_main 416
#define FID_main_c1110 417
#define FID_main_c1111 418
#define FID_main_k1112 419
#define FID_main_c1113 420
#define FID_IO_args 421
#define FID_IO_print 422
#define FID_IO_emit 423
#define FID_Clo_apply 424
#define FID_EXIT 425
#define FID_ENTER 426
CONSTV Fid FID_T[] = { { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 7, 4, 0, 1 }, { 5, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 2, 0, 0, 1 }, { 5, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 3, 0, 1 }, { 6, 0, 0, 1 }, { 9, 5, 0, 1 }, { 6, 3, 0, 1 }, { 4, 0, 0, 1 }, { 5, 3, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 6, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 1, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 4, 1, 0, 1 }, { 1, 0, 0, 1 }, { 4, 1, 0, 1 }, { 2, 0, 0, 1 }, { 5, 2, 0, 1 }, { 2, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 2, 0, 0, 1 }, { 5, 2, 0, 1 }, { 2, 0, 0, 1 }, { 6, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 2, 0, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 2, 0, 0, 1 }, { 5, 2, 0, 1 }, { 3, 0, 0, 1 }, { 4, 1, 0, 1 }, { 5, 1, 0, 1 }, { 6, 1, 0, 1 }, { 6, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 6, 0, 0, 1 }, { 4, 1, 0, 1 }, { 6, 2, 0, 1 }, { 2, 0, 0, 1 }, { 5, 1, 0, 1 }, { 3, 0, 0, 1 }, { 6, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 3, 0, 0, 1 }, { 6, 1, 0, 1 }, { 1, 0, 0, 1 }, { 4, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 5, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 3, 0, 0, 1 }, { 6, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 6, 5, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 4, 0, 0, 1 }, { 7, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 2, 0, 0, 1 }, { 4, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 2, 0, 1 }, { 3, 0, 0, 1 }, { 4, 1, 0, 1 }, { 6, 2, 0, 1 }, { 6, 0, 0, 1 }, { 3, 1, 0, 1 }, { 3, 1, 0, 1 }, { 6, 0, 0, 1 }, { 3, 1, 0, 1 }, { 2, 0, 0, 1 }, { 5, 2, 0, 1 }, { 4, 0, 0, 1 }, { 4, 0, 0, 1 }, { 5, 1, 0, 1 }, { 6, 1, 0, 1 }, { 7, 1, 0, 1 }, { 8, 1, 0, 1 }, { 5, 0, 0, 1 }, { 6, 1, 0, 1 }, { 7, 1, 0, 1 }, { 8, 1, 0, 1 }, { 9, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 6, 0, 0, 1 }, { 9, 5, 0, 1 }, { 6, 3, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 3, 1, 0, 1 }, { 3, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 6, 0, 0, 1 }, { 4, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 5, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 6, 6, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 5, 1, 0, 1 }, { 6, 0, 0, 1 }, { 5, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 2, 0, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 4, 4, 0, 1 }, { 5, 3, 0, 1 }, { 6, 3, 0, 1 }, { 3, 0, 0, 1 }, { 5, 2, 0, 1 }, { 5, 0, 0, 1 }, { 6, 3, 0, 1 }, { 2, 1, 0, 1 }, { 4, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 3, 0, 0, 1 }, { 6, 0, 0, 1 }, { 4, 1, 0, 1 }, { 9, 0, 0, 1 }, { 5, 1, 0, 1 }, { 5, 1, 0, 1 }, { 8, 2, 0, 1 }, { 5, 1, 0, 1 }, { 8, 2, 0, 1 }, { 5, 1, 0, 1 }, { 8, 2, 0, 1 }, { 5, 1, 0, 1 }, { 5, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 0, 0, 1 }, { 7, 4, 0, 1 }, { 5, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 4, 4, 0, 1 }, { 5, 3, 0, 1 }, { 6, 0, 0, 1 }, { 9, 5, 0, 1 }, { 6, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 6, 6, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 7, 5, 0, 1 }, { 4, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 6, 5, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 2, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 5, 3, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 5, 3, 0, 1 }, { 6, 3, 0, 1 }, { 8, 4, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 5, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 7, 7, 0, 1 }, { 9, 4, 0, 1 }, { 10, 3, 0, 1 }, { 6, 6, 0, 1 }, { 7, 3, 0, 1 }, { 1, 0, 0, 1 }, { 4, 4, 0, 1 }, { 9, 4, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 3, 3, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 6, 5, 0, 1 }, { 1, 0, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 0, 0, 1 }, { 4, 4, 0, 1 }, { 5, 3, 0, 1 }, { 7, 0, 0, 1 }, { 11, 6, 0, 1 }, { 5, 5, 0, 1 }, { 6, 1, 0, 1 }, { 4, 0, 0, 1 }, { 4, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 1, 0, 1 }, { 1, 0, 0, 1 }, { 5, 5, 0, 1 }, { 6, 1, 0, 1 }, { 1, 0, 0, 1 }, { 2, 2, 0, 1 }, { 2, 1, 0, 1 }, { 8, 0, 0, 1 }, { 4, 4, 0, 1 }, { 7, 7, 0, 1 }, { 2, 0, 0, 1 }, { 3, 3, 0, 1 }, { 5, 4, 0, 1 }, { 11, 8, 0, 1 }, { 14, 5, 0, 1 }, { 7, 1, 0, 1 }, { 3, 3, 0, 1 }, { 4, 4, 0, 1 }, { 8, 6, 0, 1 }, { 9, 3, 0, 1 }, { 12, 5, 0, 1 }, { 13, 3, 0, 1 }, { 4, 4, 0, 1 }, { 5, 3, 0, 1 }, { 7, 7, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 1, 1, 0, 1 }, { 2, 2, 0, 1 }, { 4, 4, 0, 1 }, { 6, 4, 0, 1 }, { 8, 4, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 6, 3, 0, 1 }, { 7, 3, 0, 1 }, { 5, 1, 0, 1 }, { 4, 1, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 7, 5, 0, 1 }, { 8, 3, 0, 1 }, { 9, 9, 0, 1 }, { 11, 11, 0, 1 }, { 6, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 1, 0, 1 }, { 2, 2, 0, 1 }, { 9, 9, 0, 1 }, { 4, 4, 0, 1 }, { 3, 3, 0, 1 }, { 4, 3, 0, 1 }, { 3, 3, 0, 1 }, { 2, 1, 0, 1 }, { 2, 0, 0, 1 }, { 4, 4, 0, 1 }, { 7, 7, 0, 1 }, { 8, 0, 0, 1 }, { 8, 8, 0, 1 }, { 7, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 1, 0, 1 }, { 2, 0, 0, 1 }, { 2, 0, 0, 1 }, { 8, 8, 0, 1 }, { 9, 0, 0, 1 }, { 2, 1, 0, 1 }, { 10, 8, 0, 1 }, { 2, 1, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 3, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 5, 2, 0, 1 }, { 1, 1, 0, 1 }, { 9, 8, 0, 1 }, { 1, 1, 0, 1 }, { 3, 0, 0, 1 }, { 3, 0, 0, 1 }, { 2, 1, 0, 1 }, { 0, 0, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 2, 0, 1 }, { 1, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 }, { 1, 0, 0, 1 }, { 2, 0, 0, 1 } };
CONSTV Cid CID_T[] = { { 2, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 2, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 0, 1, 0 }, { 1, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 0, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 1, 1, 0 }, { 3, 0, 0 }, { 6, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 5, 0, 0 }, { 0, 0, 0 }, { 5, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 3, 1, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 3, 1, 0 }, { 7, 0, 0 }, { 4, 0, 0 }, { 8, 0, 0 }, { 5, 0, 0 }, { 6, 0, 0 }, { 3, 0, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 3, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 4, 0, 0 }, { 2, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 3, 0, 0 }, { 3, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 2, 0, 0 }, { 3, 1, 0 }, { 2, 0, 0 }, { 5, 0, 0 }, { 2, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 4, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 2, 1, 0 }, { 5, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 2, 1, 0 }, { 0, 1, 0 }, { 1, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 4, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 2, 1, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 2, 0, 0 }, { 0, 1, 0 }, { 0, 1, 0 }, { 3, 1, 0 }, { 3, 1, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 3, 0, 0 }, { 2, 1, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 3, 1, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 0 }, { 2, 0, 0 }, { 4, 0, 0 }, { 1, 0, 0 }, { 2, 0, 0 }, { 4, 0, 0 }, { 1, 0, 0 }, { 0, 0, 0 }, { 1, 0, 0 }, { 2, 0, 0 } };
#define STAT_LEN 1650

#define WL_RESW 11
#define BANGS   0

#define WL_BANK Term r0, r1, r2, r3, r4, r5, rp, r6, r7, r8, r9, r10;

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
  }

#define WL_SAVE(V) (V)[0] = r0; (V)[1] = r1; (V)[2] = r2; (V)[3] = r3; (V)[4] = r4; (V)[5] = r5; (V)[6] = r6; (V)[7] = r7; (V)[8] = r8; (V)[9] = r9; (V)[10] = r10;

#define WL_TAKE(V) r0 = (V)[0]; r1 = (V)[1]; r2 = (V)[2]; r3 = (V)[3]; r4 = (V)[4]; r5 = (V)[5]; r6 = (V)[6]; r7 = (V)[7]; r8 = (V)[8]; r9 = (V)[9]; r10 = (V)[10];

#define WL_SIG Env e, DEV Term* sp, u32 seq, u32 rn, Term r0, Term r1, Term r2, Term r3, Term r4, Term r5, Term rp, Term r6, Term r7, Term r8, Term r9, Term r10

#define WL_ALL e, sp, seq, rn, r0, r1, r2, r3, r4, r5, rp, r6, r7, r8, r9, r10

#define WL_TABLE WL_X(FID_ffi_workflow_get_row) WL_X(FID_ffi_workflow_get_row_k50) WL_X(FID_ffi_workflow_get_row_k51) WL_X(FID_wire_get_list_go_7) WL_X(FID_wire_get_list_go_7_k53) WL_X(FID_wire_get_list_go_7_k54) WL_X(FID_ffi_job_get_end) WL_X(FID_ffi_job_get_end_k77) WL_X(FID_ffi_job_get_end_k78) WL_X(FID_wire_put_list_go_9) WL_X(FID_wire_put_list_go_9_k84) WL_X(FID_doc_seen_fits) WL_X(FID_doc_seen_fits_k95) WL_X(FID_ffi_workflow_get_sts) WL_X(FID_ffi_workflow_get_sts_k100) WL_X(FID_ffi_workflow_get_pool) WL_X(FID_ffi_workflow_get_pool_k105) WL_X(FID_ffi_workflow_get_pool_k106) WL_X(FID_ffi_aux_fallback_get_key) WL_X(FID_ffi_aux_fallback_get_key_k111) WL_X(FID_ffi_aux_fallback_get_key_k112) WL_X(FID_ffi_aux_fallback_get_key_k113) WL_X(FID_wire_get_list_go_1) WL_X(FID_wire_get_list_go_1_k115) WL_X(FID_wire_get_list_go_1_k116) WL_X(FID_wire_get_list_go_6) WL_X(FID_wire_get_list_go_6_k132) WL_X(FID_wire_get_list_go_6_k133) WL_X(FID_wire_put_str_go) WL_X(FID_wire_put_str_go_k135) WL_X(FID_ffi_child_get_mode) WL_X(FID_ffi_child_get_mode_k151) WL_X(FID_ffi_job_get_code) WL_X(FID_ffi_job_get_code_k157) WL_X(FID_ffi_job_get_code_k158) WL_X(FID_wire_put_list_9) WL_X(FID_wire_put_list_9_k164) WL_X(FID_admission_lv_mark) WL_X(FID_admission_lv_mark_k170) WL_X(FID_ffi_doc_seen_get_mnat) WL_X(FID_ffi_doc_seen_get_mnat_k177) WL_X(FID_ffi_doc_seen_get_mnat_k178) WL_X(FID_List_length) WL_X(FID_List_length_k184) WL_X(FID_doc_seen_whole_go) WL_X(FID_List_take) WL_X(FID_List_take_k188) WL_X(FID_doc_seen_shows) WL_X(FID_doc_seen_shows_k190) WL_X(FID_doc_seen_lines) WL_X(FID_doc_seen_lines_k192) WL_X(FID_wire_put_list_go_6) WL_X(FID_wire_put_list_go_6_k194) WL_X(FID_wire_put_list_go_5) WL_X(FID_wire_put_list_go_5_k196) WL_X(FID_wire_get_list_7) WL_X(FID_wire_get_list_7_k201) WL_X(FID_wire_get_list_7_k202) WL_X(FID_wire_put_list_go_1) WL_X(FID_wire_put_list_go_1_k227) WL_X(FID_wire_put_list_go_2) WL_X(FID_wire_put_list_go_2_k229) WL_X(FID_ffi_default_model_get_next) WL_X(FID_ffi_default_model_get_next_k233) WL_X(FID_ffi_default_model_get_next_k234) WL_X(FID_wire_take) WL_X(FID_wire_take_k244) WL_X(FID_wire_put_str) WL_X(FID_wire_put_str_k248) WL_X(FID_ffi_child_get_report) WL_X(FID_ffi_child_get_report_k255) WL_X(FID_ffi_child_get_fate) WL_X(FID_ffi_child_get_fate_k262) WL_X(FID_ffi_child_get_obs) WL_X(FID_ffi_child_get_obs_k271) WL_X(FID_ffi_child_get_obs_k272) WL_X(FID_wire_put_list_go_0) WL_X(FID_wire_put_list_go_0_k290) WL_X(FID_admission_lv_pick) WL_X(FID_admission_lv_pick_k292) WL_X(FID_admission_lv_pick_k293) WL_X(FID_admission_lv_pick_k294) WL_X(FID_admission_lv_pick_k295) WL_X(FID_admission_lv_waits) WL_X(FID_admission_lv_waits_k297) WL_X(FID_admission_lv_waits_k298) WL_X(FID_admission_lv_grant_go) WL_X(FID_admission_lv_grant_go_k300) WL_X(FID_admission_lv_grant_go_k301) WL_X(FID_admission_lv_drop) WL_X(FID_admission_lv_drop_k303) WL_X(FID_admission_lv_set) WL_X(FID_admission_lv_set_k306) WL_X(FID_admission_lv_held) WL_X(FID_admission_lv_held_k308) WL_X(FID_admission_lv_held_k309) WL_X(FID_admission_lv_cnt) WL_X(FID_admission_lv_cnt_k314) WL_X(FID_admission_lv_preempt) WL_X(FID_admission_lv_preempt_k320) WL_X(FID_List_append) WL_X(FID_List_append_k322) WL_X(FID_doc_seen_unseen) WL_X(FID_doc_seen_unseen_k327) WL_X(FID_wire_put_list_6) WL_X(FID_wire_put_list_6_k336) WL_X(FID_wire_put_list_5) WL_X(FID_wire_put_list_5_k338) WL_X(FID_workflow_found) WL_X(FID_workflow_found_k349) WL_X(FID_wire_get_list_1) WL_X(FID_wire_get_list_1_k357) WL_X(FID_wire_get_list_1_k358) WL_X(FID_ffi_aux_fallback_get_look) WL_X(FID_ffi_aux_fallback_get_look_k365) WL_X(FID_ffi_aux_fallback_get_look_k366) WL_X(FID_ffi_aux_fallback_get_look_k367) WL_X(FID_ffi_aux_fallback_get_sel) WL_X(FID_ffi_aux_fallback_get_sel_k371) WL_X(FID_ffi_aux_fallback_get_sel_k372) WL_X(FID_aux_fallback_listed) WL_X(FID_aux_fallback_listed_k376) WL_X(FID_wire_put_list_1) WL_X(FID_wire_put_list_1_k379) WL_X(FID_wire_get_list_6) WL_X(FID_wire_get_list_6_k401) WL_X(FID_wire_get_list_6_k402) WL_X(FID_wire_put_list_go_4) WL_X(FID_wire_put_list_go_4_k413) WL_X(FID_ffi_child_get_maybe_nat) WL_X(FID_ffi_child_get_maybe_nat_k425) WL_X(FID_ffi_child_get_maybe_nat_k426) WL_X(FID_wire_value) WL_X(FID_wire_value_k436) WL_X(FID_ffi_admission_get_cls) WL_X(FID_ffi_admission_get_cls_k455) WL_X(FID_wire_put_list_0) WL_X(FID_wire_put_list_0_k458) WL_X(FID_admission_lv_grant) WL_X(FID_admission_lv_grant_k461) WL_X(FID_admission_lv_grant_k462) WL_X(FID_admission_lv_leave) WL_X(FID_admission_lv_leave_k464) WL_X(FID_admission_lv_leave_k465) WL_X(FID_admission_lv_release) WL_X(FID_admission_lv_release_k467) WL_X(FID_admission_lv_find) WL_X(FID_admission_lv_find_k469) WL_X(FID_admission_lv_collect) WL_X(FID_admission_lv_admit_bg) WL_X(FID_admission_lv_admit_bg_k472) WL_X(FID_admission_lv_admit_bg_k473) WL_X(FID_admission_lv_admit_bg_k474) WL_X(FID_admission_lv_admit_bg_k475) WL_X(FID_admission_lv_admit_ia) WL_X(FID_admission_lv_admit_ia_k477) WL_X(FID_admission_lv_admit_ia_k478) WL_X(FID_admission_lv_admit_ia_k479) WL_X(FID_admission_lv_admit_ia_k480) WL_X(FID_ffi_doc_seen_get_at) WL_X(FID_ffi_doc_seen_get_at_k484) WL_X(FID_ffi_doc_seen_get_at_k485) WL_X(FID_wire_get_list_go_4) WL_X(FID_wire_get_list_go_4_k487) WL_X(FID_wire_get_list_go_4_k488) WL_X(FID_doc_seen_check) WL_X(FID_doc_seen_check_k490) WL_X(FID_doc_seen_check_k491) WL_X(FID_doc_seen_check_k492) WL_X(FID_doc_seen_check_k493) WL_X(FID_doc_seen_check_k494) WL_X(FID_doc_seen_check_k495) WL_X(FID_ffi_workflow_get_prior) WL_X(FID_ffi_workflow_get_prior_k502) WL_X(FID_ffi_workflow_get_prior_k503) WL_X(FID_workflow_admit) WL_X(FID_workflow_admit_k511) WL_X(FID_ffi_aux_fallback_get_route) WL_X(FID_ffi_aux_fallback_get_route_k514) WL_X(FID_ffi_aux_fallback_get_route_k515) WL_X(FID_ffi_aux_fallback_get_gate) WL_X(FID_ffi_aux_fallback_get_gate_k519) WL_X(FID_ffi_aux_fallback_get_gate_k520) WL_X(FID_ffi_aux_fallback_get_gate_k521) WL_X(FID_ffi_aux_fallback_get_gate_k522) WL_X(FID_aux_fallback_after) WL_X(FID_aux_fallback_after_k529) WL_X(FID_aux_fallback_put) WL_X(FID_aux_fallback_put_k531) WL_X(FID_wire_get_str) WL_X(FID_wire_get_str_k557) WL_X(FID_ffi_doc_lines_get_mend) WL_X(FID_ffi_doc_lines_get_mend_k565) WL_X(FID_ffi_doc_lines_get_mend_k566) WL_X(FID_doc_lines_plan) WL_X(FID_doc_lines_plan_k571) WL_X(FID_ffi_child_get_w) WL_X(FID_ffi_child_get_w_k585) WL_X(FID_ffi_child_get_w_k586) WL_X(FID_ffi_child_get_w_k587) WL_X(FID_wire_cdig_go) WL_X(FID_wire_cdig_go_k594) WL_X(FID_wire_get_nat_go) WL_X(FID_wire_get_nat_go_k597) WL_X(FID_wire_get_nat_go_k598) WL_X(FID_wire_get_nat_end) WL_X(FID_wire_get_nat_end_k600) WL_X(FID_ffi_job_get_ev) WL_X(FID_ffi_job_get_ev_k610) WL_X(FID_ffi_job_get_ev_k611) WL_X(FID_ffi_job_get_ev_k612) WL_X(FID_U32_show_go) WL_X(FID_ffi_admission_put_live) WL_X(FID_ffi_admission_put_live_k627) WL_X(FID_admission_Live_step) WL_X(FID_admission_Live_step_k629) WL_X(FID_admission_Live_step_k630) WL_X(FID_admission_Live_step_k631) WL_X(FID_admission_Live_step_k632) WL_X(FID_admission_Live_step_k633) WL_X(FID_admission_Live_step_k634) WL_X(FID_admission_Live_step_k635) WL_X(FID_admission_Live_step_k636) WL_X(FID_admission_Live_step_k637) WL_X(FID_ffi_doc_seen_get_iv) WL_X(FID_ffi_doc_seen_get_iv_k640) WL_X(FID_ffi_doc_seen_get_iv_k641) WL_X(FID_wire_get_list_go_5) WL_X(FID_wire_get_list_go_5_k643) WL_X(FID_wire_get_list_go_5_k644) WL_X(FID_ffi_progress_get_prior) WL_X(FID_ffi_progress_get_prior_k680) WL_X(FID_ffi_progress_get_prior_k681) WL_X(FID_ffi_progress_get_prior_k682) WL_X(FID_ffi_doc_lines_get_run) WL_X(FID_ffi_doc_lines_get_run_k696) WL_X(FID_ffi_doc_lines_get_run_k697) WL_X(FID_wire_get_list_go_3) WL_X(FID_wire_get_list_go_3_k699) WL_X(FID_wire_get_list_go_3_k700) WL_X(FID_ffi_child_get_ph) WL_X(FID_ffi_child_get_ph_k706) WL_X(FID_ffi_child_get_ph_k707) WL_X(FID_ffi_child_get_ph_k708) WL_X(FID_ffi_child_get_ph_k709) WL_X(FID_ffi_child_get_mfate) WL_X(FID_ffi_child_get_mfate_k712) WL_X(FID_ffi_child_get_mfate_k713) WL_X(FID_ffi_child_get_cfg) WL_X(FID_ffi_child_get_cfg_k717) WL_X(FID_ffi_child_get_cfg_k718) WL_X(FID_wire_tok) WL_X(FID_wire_tok_k725) WL_X(FID_ffi_job_get_job) WL_X(FID_ffi_job_get_job_k730) WL_X(FID_ffi_job_get_job_k731) WL_X(FID_ffi_job_get_job_k732) WL_X(FID_ffi_job_get_job_k733) WL_X(FID_ffi_job_get_job_k734) WL_X(FID_ffi_job_get_job_k735) WL_X(FID_Nat_show_fin) WL_X(FID_wire_get_list_4) WL_X(FID_wire_get_list_4_k761) WL_X(FID_wire_get_list_4_k762) WL_X(FID_ffi_default_model_get_saved) WL_X(FID_ffi_default_model_get_saved_k790) WL_X(FID_ffi_default_model_get_saved_k791) WL_X(FID_wire_get_u32) WL_X(FID_wire_get_u32_k800) WL_X(FID_ffi_doc_lines_get_end) WL_X(FID_ffi_doc_lines_get_end_k813) WL_X(FID_wire_peek) WL_X(FID_wire_peek_k828) WL_X(FID_ffi_job_get_cap) WL_X(FID_ffi_job_get_cap_k832) WL_X(FID_ffi_job_get_cap_k833) WL_X(FID_ffi_admission_get_lim) WL_X(FID_ffi_admission_get_lim_k839) WL_X(FID_ffi_admission_get_lim_k840) WL_X(FID_U32_show) WL_X(FID_ffi_admission_get_op) WL_X(FID_ffi_admission_get_op_k848) WL_X(FID_ffi_admission_get_op_k849) WL_X(FID_ffi_admission_get_op_k850) WL_X(FID_ffi_admission_get_op_k851) WL_X(FID_ffi_admission_get_op_k852) WL_X(FID_ffi_admission_get_op_k853) WL_X(FID_ffi_admission_get_op_k854) WL_X(FID_Nat_show) WL_X(FID_String_append) WL_X(FID_String_append_k860) WL_X(FID_wire_get_list_5) WL_X(FID_wire_get_list_5_k862) WL_X(FID_wire_get_list_5_k863) WL_X(FID_ffi_workflow_get_req) WL_X(FID_ffi_workflow_get_req_k869) WL_X(FID_ffi_workflow_get_req_k870) WL_X(FID_ffi_workflow_get_req_k871) WL_X(FID_ffi_workflow_get_req_k872) WL_X(FID_ffi_workflow_get_req_k873) WL_X(FID_ffi_workflow_get_req_k874) WL_X(FID_ffi_workflow_get_req_k875) WL_X(FID_ffi_workflow_get_req_k876) WL_X(FID_ffi_aux_fallback_get_req) WL_X(FID_ffi_aux_fallback_get_req_k880) WL_X(FID_ffi_aux_fallback_get_req_k881) WL_X(FID_ffi_aux_fallback_get_req_k882) WL_X(FID_ffi_aux_fallback_get_req_k883) WL_X(FID_ffi_aux_fallback_get_req_k884) WL_X(FID_ffi_aux_fallback_get_req_k885) WL_X(FID_ffi_aux_fallback_get_req_k886) WL_X(FID_ffi_aux_fallback_get_req_k887) WL_X(FID_ffi_default_model_get_in) WL_X(FID_ffi_default_model_get_in_k894) WL_X(FID_ffi_default_model_get_in_k895) WL_X(FID_ffi_sandbox_get_doc) WL_X(FID_ffi_sandbox_get_doc_k908) WL_X(FID_ffi_sandbox_get_doc_k909) WL_X(FID_wire_get_list_3) WL_X(FID_wire_get_list_3_k914) WL_X(FID_wire_get_list_3_k915) WL_X(FID_wire_get_nat) WL_X(FID_wire_get_nat_k930) WL_X(FID_wire_get_nat_k931) WL_X(FID_ffi_admission_get_open) WL_X(FID_ffi_admission_get_open_k938) WL_X(FID_ffi_admission_get_open_k939) WL_X(FID_ffi_admission_step) WL_X(FID_ffi_admission_step_k945) WL_X(FID_ffi_admission_step_k946) WL_X(FID_ffi_admission_step_k947) WL_X(FID_ffi_echo_step) WL_X(FID_ffi_echo_step_k950) WL_X(FID_ffi_echo_step_k951) WL_X(FID_ffi_echo_step_k952) WL_X(FID_ffi_admission_open) WL_X(FID_ffi_admission_open_k1009) WL_X(FID_ffi_admission_open_k1010) WL_X(FID_ffi_echo_open) WL_X(FID_ffi_echo_open_k1014) WL_X(FID_ffi_echo_open_k1015) WL_X(FID_step_go) WL_X(FID_step_go_k1018) WL_X(FID_step_go_k1019) WL_X(FID_ffi_go) WL_X(FID_ffi_go_k1022) WL_X(FID_ffi_go_k1023) WL_X(FID_ffi_go_k1024) WL_X(FID_ffi_go_k1025) WL_X(FID_ffi_go_k1026) WL_X(FID_ffi_go_k1027) WL_X(FID_ffi_go_k1028) WL_X(FID_ffi_go_k1029) WL_X(FID_ffi_go_k1030) WL_X(FID_ffi_go_k1031) WL_X(FID_ffi_go_k1032) WL_X(FID_ffi_go_k1033) WL_X(FID_ffi_go_k1034) WL_X(FID_ffi_go_k1035) WL_X(FID_ffi_go_k1036) WL_X(FID_ffi_go_k1037) WL_X(FID_ffi_go_k1038) WL_X(FID_ffi_go_k1039) WL_X(FID_ffi_go_k1040) WL_X(FID_ffi_go_k1041) WL_X(FID_ffi_go_k1042) WL_X(FID_ffi_go_k1043) WL_X(FID_ffi_go_k1044) WL_X(FID_ffi_go_k1045) WL_X(FID_ffi_go_k1046) WL_X(FID_ffi_go_k1047) WL_X(FID_ffi_go_k1048) WL_X(FID_ffi_go_k1049) WL_X(FID_ffi_go_k1050) WL_X(FID_ffi_go_k1051) WL_X(FID_ffi_go_k1052) WL_X(FID_ffi_go_k1053) WL_X(FID_ffi_go_k1054) WL_X(FID_ffi_go_k1055) WL_X(FID_ffi_go_k1056) WL_X(FID_ffi_go_k1057) WL_X(FID_ffi_go_k1058) WL_X(FID_ffi_go_k1059) WL_X(FID_ffi_go_k1060) WL_X(FID_ffi_go_k1061) WL_X(FID_ffi_go_k1062) WL_X(FID_ffi_go_k1063) WL_X(FID_ffi_go_k1064) WL_X(FID_open_go) WL_X(FID_open_go_k1068) WL_X(FID_open_go_k1069) WL_X(FID_step) WL_X(FID_step_k1071) WL_X(FID_close) WL_X(FID_ffi) WL_X(FID_ffi_k1075) WL_X(FID_U32_read_go) WL_X(FID_open) WL_X(FID_open_k1080) WL_X(FID_cli_steps) WL_X(FID_cli_steps_k1082) WL_X(FID_cli_steps_k1083) WL_X(FID_cli_steps_k1084) WL_X(FID_U32_read) WL_X(FID_cli_print) WL_X(FID_cli_print_c1096) WL_X(FID_cli_print_c1097) WL_X(FID_cli_print_c1098) WL_X(FID_cli_args) WL_X(FID_cli_args_k1100) WL_X(FID_cli_args_k1101) WL_X(FID_cli_args_k1102) WL_X(FID_cli_args_k1103) WL_X(FID_IO_bind) WL_X(FID_IO_bind_c1107) WL_X(FID_IO_bind_k1108) WL_X(FID_main) WL_X(FID_main_c1110) WL_X(FID_main_c1111) WL_X(FID_main_k1112) WL_X(FID_main_c1113) WL_X(FID_IO_args) WL_X(FID_IO_print) WL_X(FID_IO_emit) WL_X(FID_Clo_apply) WL_X(FID_EXIT)
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

CONSTV u64 STAT_IMG[] = { 114ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 0), 118ull, term_ctr(CID_SCon, STAT_OFF + 2), 111ull, term_ctr(CID_SCon, STAT_OFF + 4), 32ull, term_ctr(CID_SCon, STAT_OFF + 6), 116ull, term_ctr(CID_SCon, STAT_OFF + 8), 102ull, term_ctr(CID_SCon, STAT_OFF + 10), 101ull, term_ctr(CID_SCon, STAT_OFF + 12), 108ull, term_ctr(CID_SCon, STAT_OFF + 14), 32ull, term_ctr(CID_SCon, STAT_OFF + 16), 116ull, term_ctr(CID_SCon, STAT_OFF + 18), 117ull, term_ctr(CID_SCon, STAT_OFF + 20), 112ull, term_ctr(CID_SCon, STAT_OFF + 22), 110ull, term_ctr(CID_SCon, STAT_OFF + 24), 105ull, term_ctr(CID_SCon, STAT_OFF + 26), 32ull, term_ctr(CID_SCon, STAT_OFF + 28), 58ull, term_ctr(CID_SCon, STAT_OFF + 30), 100ull, term_ctr(CID_SCon, STAT_OFF + 32), 108ull, term_ctr(CID_SCon, STAT_OFF + 34), 105ull, term_ctr(CID_SCon, STAT_OFF + 36), 104ull, term_ctr(CID_SCon, STAT_OFF + 38), 99ull, term_ctr(CID_SCon, STAT_OFF + 40), 101ull, term_pak(CID_SNil, 0), 100ull, term_ctr(CID_SCon, STAT_OFF + 44), 111ull, term_ctr(CID_SCon, STAT_OFF + 46), 109ull, term_ctr(CID_SCon, STAT_OFF + 48), 32ull, term_ctr(CID_SCon, STAT_OFF + 50), 100ull, term_ctr(CID_SCon, STAT_OFF + 52), 97ull, term_ctr(CID_SCon, STAT_OFF + 54), 98ull, term_ctr(CID_SCon, STAT_OFF + 56), 32ull, term_ctr(CID_SCon, STAT_OFF + 58), 58ull, term_ctr(CID_SCon, STAT_OFF + 60), 100ull, term_ctr(CID_SCon, STAT_OFF + 62), 108ull, term_ctr(CID_SCon, STAT_OFF + 64), 105ull, term_ctr(CID_SCon, STAT_OFF + 66), 104ull, term_ctr(CID_SCon, STAT_OFF + 68), 99ull, term_ctr(CID_SCon, STAT_OFF + 70), 108ull, term_pak(CID_SNil, 0), 108ull, term_ctr(CID_SCon, STAT_OFF + 74), 111ull, term_ctr(CID_SCon, STAT_OFF + 76), 112ull, term_ctr(CID_SCon, STAT_OFF + 78), 32ull, term_ctr(CID_SCon, STAT_OFF + 80), 100ull, term_ctr(CID_SCon, STAT_OFF + 82), 97ull, term_ctr(CID_SCon, STAT_OFF + 84), 98ull, term_ctr(CID_SCon, STAT_OFF + 86), 32ull, term_ctr(CID_SCon, STAT_OFF + 88), 58ull, term_ctr(CID_SCon, STAT_OFF + 90), 100ull, term_ctr(CID_SCon, STAT_OFF + 92), 108ull, term_ctr(CID_SCon, STAT_OFF + 94), 105ull, term_ctr(CID_SCon, STAT_OFF + 96), 104ull, term_ctr(CID_SCon, STAT_OFF + 98), 99ull, term_ctr(CID_SCon, STAT_OFF + 100), term_pak(CID_job_Killed, 0), term_pak(CID_Nil, 0), 115ull, term_ctr(CID_SCon, STAT_OFF + 32), 115ull, term_ctr(CID_SCon, STAT_OFF + 106), 101ull, term_ctr(CID_SCon, STAT_OFF + 108), 114ull, term_ctr(CID_SCon, STAT_OFF + 110), 103ull, term_ctr(CID_SCon, STAT_OFF + 112), 111ull, term_ctr(CID_SCon, STAT_OFF + 114), 114ull, term_ctr(CID_SCon, STAT_OFF + 116), 112ull, term_ctr(CID_SCon, STAT_OFF + 118), 116ull, term_pak(CID_SNil, 0), 115ull, term_ctr(CID_SCon, STAT_OFF + 122), 101ull, term_ctr(CID_SCon, STAT_OFF + 124), 117ull, term_ctr(CID_SCon, STAT_OFF + 126), 113ull, term_ctr(CID_SCon, STAT_OFF + 128), 101ull, term_ctr(CID_SCon, STAT_OFF + 130), 114ull, term_ctr(CID_SCon, STAT_OFF + 132), 32ull, term_ctr(CID_SCon, STAT_OFF + 134), 101ull, term_ctr(CID_SCon, STAT_OFF + 136), 114ull, term_ctr(CID_SCon, STAT_OFF + 138), 105ull, term_ctr(CID_SCon, STAT_OFF + 140), 119ull, term_ctr(CID_SCon, STAT_OFF + 142), 32ull, term_ctr(CID_SCon, STAT_OFF + 144), 100ull, term_ctr(CID_SCon, STAT_OFF + 146), 101ull, term_ctr(CID_SCon, STAT_OFF + 148), 109ull, term_ctr(CID_SCon, STAT_OFF + 150), 114ull, term_ctr(CID_SCon, STAT_OFF + 152), 111ull, term_ctr(CID_SCon, STAT_OFF + 154), 102ull, term_ctr(CID_SCon, STAT_OFF + 156), 108ull, term_ctr(CID_SCon, STAT_OFF + 158), 97ull, term_ctr(CID_SCon, STAT_OFF + 160), 109ull, term_ctr(CID_SCon, STAT_OFF + 162), 115ull, term_pak(CID_SNil, 0), 109ull, term_ctr(CID_SCon, STAT_OFF + 166), 32ull, term_ctr(CID_SCon, STAT_OFF + 168), 100ull, term_ctr(CID_SCon, STAT_OFF + 170), 101ull, term_ctr(CID_SCon, STAT_OFF + 172), 115ull, term_ctr(CID_SCon, STAT_OFF + 174), 112ull, term_ctr(CID_SCon, STAT_OFF + 176), 97ull, term_ctr(CID_SCon, STAT_OFF + 178), 108ull, term_ctr(CID_SCon, STAT_OFF + 180), 101ull, term_ctr(CID_SCon, STAT_OFF + 182), 32ull, term_ctr(CID_SCon, STAT_OFF + 184), 100ull, term_ctr(CID_SCon, STAT_OFF + 186), 97ull, term_ctr(CID_SCon, STAT_OFF + 188), 98ull, term_ctr(CID_SCon, STAT_OFF + 190), 32ull, term_ctr(CID_SCon, STAT_OFF + 192), 58ull, term_ctr(CID_SCon, STAT_OFF + 194), 100ull, term_ctr(CID_SCon, STAT_OFF + 196), 108ull, term_ctr(CID_SCon, STAT_OFF + 198), 105ull, term_ctr(CID_SCon, STAT_OFF + 200), 104ull, term_ctr(CID_SCon, STAT_OFF + 202), 99ull, term_ctr(CID_SCon, STAT_OFF + 204), 98ull, term_ctr(CID_SCon, STAT_OFF + 32), 111ull, term_ctr(CID_SCon, STAT_OFF + 208), 106ull, term_ctr(CID_SCon, STAT_OFF + 210), 107ull, term_pak(CID_SNil, 0), 114ull, term_ctr(CID_SCon, STAT_OFF + 214), 111ull, term_ctr(CID_SCon, STAT_OFF + 216), 119ull, term_ctr(CID_SCon, STAT_OFF + 218), 32ull, term_ctr(CID_SCon, STAT_OFF + 220), 100ull, term_ctr(CID_SCon, STAT_OFF + 222), 97ull, term_ctr(CID_SCon, STAT_OFF + 224), 98ull, term_ctr(CID_SCon, STAT_OFF + 226), 32ull, term_ctr(CID_SCon, STAT_OFF + 228), 58ull, term_ctr(CID_SCon, STAT_OFF + 230), 115ull, term_ctr(CID_SCon, STAT_OFF + 232), 115ull, term_ctr(CID_SCon, STAT_OFF + 234), 101ull, term_ctr(CID_SCon, STAT_OFF + 236), 114ull, term_ctr(CID_SCon, STAT_OFF + 238), 103ull, term_ctr(CID_SCon, STAT_OFF + 240), 111ull, term_ctr(CID_SCon, STAT_OFF + 242), 114ull, term_ctr(CID_SCon, STAT_OFF + 244), 112ull, term_ctr(CID_SCon, STAT_OFF + 246), 120ull, term_ctr(CID_SCon, STAT_OFF + 32), 111ull, term_ctr(CID_SCon, STAT_OFF + 250), 98ull, term_ctr(CID_SCon, STAT_OFF + 252), 100ull, term_ctr(CID_SCon, STAT_OFF + 254), 110ull, term_ctr(CID_SCon, STAT_OFF + 256), 97ull, term_ctr(CID_SCon, STAT_OFF + 258), 115ull, term_ctr(CID_SCon, STAT_OFF + 260), 103ull, term_pak(CID_SNil, 0), 97ull, term_ctr(CID_SCon, STAT_OFF + 264), 108ull, term_ctr(CID_SCon, STAT_OFF + 266), 102ull, term_ctr(CID_SCon, STAT_OFF + 268), 32ull, term_ctr(CID_SCon, STAT_OFF + 270), 101ull, term_ctr(CID_SCon, STAT_OFF + 272), 116ull, term_ctr(CID_SCon, STAT_OFF + 274), 101ull, term_ctr(CID_SCon, STAT_OFF + 276), 108ull, term_ctr(CID_SCon, STAT_OFF + 278), 101ull, term_ctr(CID_SCon, STAT_OFF + 280), 100ull, term_ctr(CID_SCon, STAT_OFF + 282), 32ull, term_ctr(CID_SCon, STAT_OFF + 284), 100ull, term_ctr(CID_SCon, STAT_OFF + 286), 97ull, term_ctr(CID_SCon, STAT_OFF + 288), 98ull, term_ctr(CID_SCon, STAT_OFF + 290), 32ull, term_ctr(CID_SCon, STAT_OFF + 292), 58ull, term_ctr(CID_SCon, STAT_OFF + 294), 100ull, term_ctr(CID_SCon, STAT_OFF + 296), 108ull, term_ctr(CID_SCon, STAT_OFF + 298), 105ull, term_ctr(CID_SCon, STAT_OFF + 300), 104ull, term_ctr(CID_SCon, STAT_OFF + 302), 99ull, term_ctr(CID_SCon, STAT_OFF + 304), 100ull, term_pak(CID_SNil, 0), 105ull, term_ctr(CID_SCon, STAT_OFF + 308), 32ull, term_ctr(CID_SCon, STAT_OFF + 310), 100ull, term_ctr(CID_SCon, STAT_OFF + 312), 97ull, term_ctr(CID_SCon, STAT_OFF + 314), 98ull, term_ctr(CID_SCon, STAT_OFF + 316), 32ull, term_ctr(CID_SCon, STAT_OFF + 318), 58ull, term_ctr(CID_SCon, STAT_OFF + 320), 100ull, term_ctr(CID_SCon, STAT_OFF + 322), 108ull, term_ctr(CID_SCon, STAT_OFF + 324), 105ull, term_ctr(CID_SCon, STAT_OFF + 326), 104ull, term_ctr(CID_SCon, STAT_OFF + 328), 99ull, term_ctr(CID_SCon, STAT_OFF + 330), 99ull, term_ctr(CID_SCon, STAT_OFF + 214), 111ull, term_ctr(CID_SCon, STAT_OFF + 334), 108ull, term_ctr(CID_SCon, STAT_OFF + 336), 99ull, term_ctr(CID_SCon, STAT_OFF + 338), 32ull, term_ctr(CID_SCon, STAT_OFF + 340), 100ull, term_ctr(CID_SCon, STAT_OFF + 342), 97ull, term_ctr(CID_SCon, STAT_OFF + 344), 98ull, term_ctr(CID_SCon, STAT_OFF + 346), 32ull, term_ctr(CID_SCon, STAT_OFF + 348), 58ull, term_ctr(CID_SCon, STAT_OFF + 350), 100ull, term_ctr(CID_SCon, STAT_OFF + 352), 108ull, term_ctr(CID_SCon, STAT_OFF + 354), 105ull, term_ctr(CID_SCon, STAT_OFF + 356), 104ull, term_ctr(CID_SCon, STAT_OFF + 358), 99ull, term_ctr(CID_SCon, STAT_OFF + 360), 57ull, term_pak(CID_Nil, 0), 56ull, term_ctr(CID_Con, STAT_OFF + 364), 55ull, term_ctr(CID_Con, STAT_OFF + 366), 54ull, term_ctr(CID_Con, STAT_OFF + 368), 53ull, term_ctr(CID_Con, STAT_OFF + 370), 52ull, term_ctr(CID_Con, STAT_OFF + 372), 51ull, term_ctr(CID_Con, STAT_OFF + 374), 50ull, term_ctr(CID_Con, STAT_OFF + 376), 49ull, term_ctr(CID_Con, STAT_OFF + 378), 48ull, term_ctr(CID_Con, STAT_OFF + 380), 110ull, term_ctr(CID_SCon, STAT_OFF + 122), 101ull, term_ctr(CID_SCon, STAT_OFF + 384), 118ull, term_ctr(CID_SCon, STAT_OFF + 386), 101ull, term_ctr(CID_SCon, STAT_OFF + 388), 32ull, term_ctr(CID_SCon, STAT_OFF + 390), 100ull, term_ctr(CID_SCon, STAT_OFF + 392), 97ull, term_ctr(CID_SCon, STAT_OFF + 394), 98ull, term_ctr(CID_SCon, STAT_OFF + 396), 32ull, term_ctr(CID_SCon, STAT_OFF + 398), 58ull, term_ctr(CID_SCon, STAT_OFF + 400), 98ull, term_ctr(CID_SCon, STAT_OFF + 402), 111ull, term_ctr(CID_SCon, STAT_OFF + 404), 106ull, term_ctr(CID_SCon, STAT_OFF + 406), 110ull, term_ctr(CID_SCon, STAT_OFF + 32), 101ull, term_ctr(CID_SCon, STAT_OFF + 410), 101ull, term_ctr(CID_SCon, STAT_OFF + 412), 115ull, term_ctr(CID_SCon, STAT_OFF + 414), 95ull, term_ctr(CID_SCon, STAT_OFF + 416), 99ull, term_ctr(CID_SCon, STAT_OFF + 418), 111ull, term_ctr(CID_SCon, STAT_OFF + 420), 100ull, term_ctr(CID_SCon, STAT_OFF + 422), 101ull, term_ctr(CID_SCon, STAT_OFF + 334), 104ull, term_ctr(CID_SCon, STAT_OFF + 426), 99ull, term_ctr(CID_SCon, STAT_OFF + 428), 32ull, term_ctr(CID_SCon, STAT_OFF + 430), 114ull, term_ctr(CID_SCon, STAT_OFF + 432), 111ull, term_ctr(CID_SCon, STAT_OFF + 434), 105ull, term_ctr(CID_SCon, STAT_OFF + 436), 114ull, term_ctr(CID_SCon, STAT_OFF + 438), 112ull, term_ctr(CID_SCon, STAT_OFF + 440), 32ull, term_ctr(CID_SCon, STAT_OFF + 442), 100ull, term_ctr(CID_SCon, STAT_OFF + 444), 97ull, term_ctr(CID_SCon, STAT_OFF + 446), 98ull, term_ctr(CID_SCon, STAT_OFF + 448), 32ull, term_ctr(CID_SCon, STAT_OFF + 450), 58ull, term_ctr(CID_SCon, STAT_OFF + 452), 115ull, term_ctr(CID_SCon, STAT_OFF + 454), 115ull, term_ctr(CID_SCon, STAT_OFF + 456), 101ull, term_ctr(CID_SCon, STAT_OFF + 458), 114ull, term_ctr(CID_SCon, STAT_OFF + 460), 103ull, term_ctr(CID_SCon, STAT_OFF + 462), 111ull, term_ctr(CID_SCon, STAT_OFF + 464), 114ull, term_ctr(CID_SCon, STAT_OFF + 466), 112ull, term_ctr(CID_SCon, STAT_OFF + 468), 116ull, term_ctr(CID_SCon, STAT_OFF + 386), 110ull, term_ctr(CID_SCon, STAT_OFF + 472), 111ull, term_ctr(CID_SCon, STAT_OFF + 474), 99ull, term_ctr(CID_SCon, STAT_OFF + 476), 32ull, term_ctr(CID_SCon, STAT_OFF + 478), 100ull, term_ctr(CID_SCon, STAT_OFF + 480), 108ull, term_ctr(CID_SCon, STAT_OFF + 482), 105ull, term_ctr(CID_SCon, STAT_OFF + 484), 104ull, term_ctr(CID_SCon, STAT_OFF + 486), 99ull, term_ctr(CID_SCon, STAT_OFF + 488), 32ull, term_ctr(CID_SCon, STAT_OFF + 490), 100ull, term_ctr(CID_SCon, STAT_OFF + 492), 97ull, term_ctr(CID_SCon, STAT_OFF + 494), 98ull, term_ctr(CID_SCon, STAT_OFF + 496), 32ull, term_ctr(CID_SCon, STAT_OFF + 498), 58ull, term_ctr(CID_SCon, STAT_OFF + 500), 120ull, term_ctr(CID_SCon, STAT_OFF + 502), 111ull, term_ctr(CID_SCon, STAT_OFF + 504), 98ull, term_ctr(CID_SCon, STAT_OFF + 506), 100ull, term_ctr(CID_SCon, STAT_OFF + 508), 110ull, term_ctr(CID_SCon, STAT_OFF + 510), 97ull, term_ctr(CID_SCon, STAT_OFF + 512), 115ull, term_ctr(CID_SCon, STAT_OFF + 514), 101ull, term_ctr(CID_SCon, STAT_OFF + 106), 110ull, term_ctr(CID_SCon, STAT_OFF + 518), 105ull, term_ctr(CID_SCon, STAT_OFF + 520), 108ull, term_ctr(CID_SCon, STAT_OFF + 522), 95ull, term_ctr(CID_SCon, STAT_OFF + 524), 99ull, term_ctr(CID_SCon, STAT_OFF + 526), 111ull, term_ctr(CID_SCon, STAT_OFF + 528), 100ull, term_ctr(CID_SCon, STAT_OFF + 530), 115ull, term_ctr(CID_SCon, STAT_OFF + 44), 97ull, term_ctr(CID_SCon, STAT_OFF + 534), 104ull, term_ctr(CID_SCon, STAT_OFF + 536), 112ull, term_ctr(CID_SCon, STAT_OFF + 538), 32ull, term_ctr(CID_SCon, STAT_OFF + 540), 100ull, term_ctr(CID_SCon, STAT_OFF + 542), 97ull, term_ctr(CID_SCon, STAT_OFF + 544), 98ull, term_ctr(CID_SCon, STAT_OFF + 546), 32ull, term_ctr(CID_SCon, STAT_OFF + 548), 58ull, term_ctr(CID_SCon, STAT_OFF + 550), 100ull, term_ctr(CID_SCon, STAT_OFF + 552), 108ull, term_ctr(CID_SCon, STAT_OFF + 554), 105ull, term_ctr(CID_SCon, STAT_OFF + 556), 104ull, term_ctr(CID_SCon, STAT_OFF + 558), 99ull, term_ctr(CID_SCon, STAT_OFF + 560), 116ull, term_ctr(CID_SCon, STAT_OFF + 44), 97ull, term_ctr(CID_SCon, STAT_OFF + 564), 102ull, term_ctr(CID_SCon, STAT_OFF + 566), 32ull, term_ctr(CID_SCon, STAT_OFF + 568), 100ull, term_ctr(CID_SCon, STAT_OFF + 570), 97ull, term_ctr(CID_SCon, STAT_OFF + 572), 98ull, term_ctr(CID_SCon, STAT_OFF + 574), 32ull, term_ctr(CID_SCon, STAT_OFF + 576), 58ull, term_ctr(CID_SCon, STAT_OFF + 578), 100ull, term_ctr(CID_SCon, STAT_OFF + 580), 108ull, term_ctr(CID_SCon, STAT_OFF + 582), 105ull, term_ctr(CID_SCon, STAT_OFF + 584), 104ull, term_ctr(CID_SCon, STAT_OFF + 586), 99ull, term_ctr(CID_SCon, STAT_OFF + 588), 103ull, term_ctr(CID_SCon, STAT_OFF + 166), 110ull, term_ctr(CID_SCon, STAT_OFF + 592), 105ull, term_ctr(CID_SCon, STAT_OFF + 594), 116ull, term_ctr(CID_SCon, STAT_OFF + 596), 116ull, term_ctr(CID_SCon, STAT_OFF + 598), 101ull, term_ctr(CID_SCon, STAT_OFF + 600), 115ull, term_ctr(CID_SCon, STAT_OFF + 602), 32ull, term_ctr(CID_SCon, STAT_OFF + 604), 100ull, term_ctr(CID_SCon, STAT_OFF + 606), 97ull, term_ctr(CID_SCon, STAT_OFF + 608), 98ull, term_ctr(CID_SCon, STAT_OFF + 610), 32ull, term_ctr(CID_SCon, STAT_OFF + 612), 58ull, term_ctr(CID_SCon, STAT_OFF + 614), 100ull, term_ctr(CID_SCon, STAT_OFF + 616), 108ull, term_ctr(CID_SCon, STAT_OFF + 618), 105ull, term_ctr(CID_SCon, STAT_OFF + 620), 104ull, term_ctr(CID_SCon, STAT_OFF + 622), 99ull, term_ctr(CID_SCon, STAT_OFF + 624), 0, term_pak(CID_Nil, 0), 98ull, term_pak(CID_SNil, 0), 111ull, term_ctr(CID_SCon, STAT_OFF + 630), 106ull, term_ctr(CID_SCon, STAT_OFF + 632), 32ull, term_ctr(CID_SCon, STAT_OFF + 634), 100ull, term_ctr(CID_SCon, STAT_OFF + 636), 97ull, term_ctr(CID_SCon, STAT_OFF + 638), 98ull, term_ctr(CID_SCon, STAT_OFF + 640), 32ull, term_ctr(CID_SCon, STAT_OFF + 642), 58ull, term_ctr(CID_SCon, STAT_OFF + 644), 98ull, term_ctr(CID_SCon, STAT_OFF + 646), 111ull, term_ctr(CID_SCon, STAT_OFF + 648), 106ull, term_ctr(CID_SCon, STAT_OFF + 650), 111ull, term_ctr(CID_SCon, STAT_OFF + 410), 105ull, term_ctr(CID_SCon, STAT_OFF + 654), 115ull, term_ctr(CID_SCon, STAT_OFF + 656), 115ull, term_ctr(CID_SCon, STAT_OFF + 658), 105ull, term_ctr(CID_SCon, STAT_OFF + 660), 109ull, term_ctr(CID_SCon, STAT_OFF + 662), 100ull, term_ctr(CID_SCon, STAT_OFF + 664), 97ull, term_ctr(CID_SCon, STAT_OFF + 666), 32ull, term_ctr(CID_SCon, STAT_OFF + 668), 69ull, term_ctr(CID_SCon, STAT_OFF + 670), 48ull, term_pak(CID_SNil, 0), 114ull, term_ctr(CID_SCon, STAT_OFF + 166), 111ull, term_ctr(CID_SCon, STAT_OFF + 676), 104ull, term_ctr(CID_SCon, STAT_OFF + 678), 99ull, term_ctr(CID_SCon, STAT_OFF + 680), 110ull, term_ctr(CID_SCon, STAT_OFF + 682), 97ull, term_ctr(CID_SCon, STAT_OFF + 684), 32ull, term_ctr(CID_SCon, STAT_OFF + 686), 100ull, term_ctr(CID_SCon, STAT_OFF + 688), 101ull, term_ctr(CID_SCon, STAT_OFF + 690), 109ull, term_ctr(CID_SCon, STAT_OFF + 692), 114ull, term_ctr(CID_SCon, STAT_OFF + 694), 111ull, term_ctr(CID_SCon, STAT_OFF + 696), 102ull, term_ctr(CID_SCon, STAT_OFF + 698), 108ull, term_ctr(CID_SCon, STAT_OFF + 700), 97ull, term_ctr(CID_SCon, STAT_OFF + 702), 109ull, term_ctr(CID_SCon, STAT_OFF + 704), 32ull, term_ctr(CID_SCon, STAT_OFF + 706), 58ull, term_ctr(CID_SCon, STAT_OFF + 708), 110ull, term_ctr(CID_SCon, STAT_OFF + 710), 101ull, term_ctr(CID_SCon, STAT_OFF + 712), 101ull, term_ctr(CID_SCon, STAT_OFF + 714), 115ull, term_ctr(CID_SCon, STAT_OFF + 716), 95ull, term_ctr(CID_SCon, STAT_OFF + 718), 99ull, term_ctr(CID_SCon, STAT_OFF + 720), 111ull, term_ctr(CID_SCon, STAT_OFF + 722), 100ull, term_ctr(CID_SCon, STAT_OFF + 724), 119ull, term_ctr(CID_SCon, STAT_OFF + 32), 111ull, term_ctr(CID_SCon, STAT_OFF + 728), 108ull, term_ctr(CID_SCon, STAT_OFF + 730), 102ull, term_ctr(CID_SCon, STAT_OFF + 732), 107ull, term_ctr(CID_SCon, STAT_OFF + 734), 114ull, term_ctr(CID_SCon, STAT_OFF + 736), 111ull, term_ctr(CID_SCon, STAT_OFF + 738), 119ull, term_ctr(CID_SCon, STAT_OFF + 740), 107ull, term_ctr(CID_SCon, STAT_OFF + 32), 99ull, term_ctr(CID_SCon, STAT_OFF + 744), 97ull, term_ctr(CID_SCon, STAT_OFF + 746), 98ull, term_ctr(CID_SCon, STAT_OFF + 748), 108ull, term_ctr(CID_SCon, STAT_OFF + 750), 108ull, term_ctr(CID_SCon, STAT_OFF + 752), 97ull, term_ctr(CID_SCon, STAT_OFF + 754), 102ull, term_ctr(CID_SCon, STAT_OFF + 756), 95ull, term_ctr(CID_SCon, STAT_OFF + 758), 120ull, term_ctr(CID_SCon, STAT_OFF + 760), 117ull, term_ctr(CID_SCon, STAT_OFF + 762), 97ull, term_ctr(CID_SCon, STAT_OFF + 764), 108ull, term_ctr(CID_SCon, STAT_OFF + 32), 101ull, term_ctr(CID_SCon, STAT_OFF + 768), 100ull, term_ctr(CID_SCon, STAT_OFF + 770), 111ull, term_ctr(CID_SCon, STAT_OFF + 772), 109ull, term_ctr(CID_SCon, STAT_OFF + 774), 95ull, term_ctr(CID_SCon, STAT_OFF + 776), 116ull, term_ctr(CID_SCon, STAT_OFF + 778), 108ull, term_ctr(CID_SCon, STAT_OFF + 780), 117ull, term_ctr(CID_SCon, STAT_OFF + 782), 97ull, term_ctr(CID_SCon, STAT_OFF + 784), 102ull, term_ctr(CID_SCon, STAT_OFF + 786), 101ull, term_ctr(CID_SCon, STAT_OFF + 788), 100ull, term_ctr(CID_SCon, STAT_OFF + 790), 112ull, term_pak(CID_SNil, 0), 97ull, term_ctr(CID_SCon, STAT_OFF + 794), 99ull, term_ctr(CID_SCon, STAT_OFF + 796), 32ull, term_ctr(CID_SCon, STAT_OFF + 798), 100ull, term_ctr(CID_SCon, STAT_OFF + 800), 97ull, term_ctr(CID_SCon, STAT_OFF + 802), 98ull, term_ctr(CID_SCon, STAT_OFF + 804), 32ull, term_ctr(CID_SCon, STAT_OFF + 806), 58ull, term_ctr(CID_SCon, STAT_OFF + 808), 115ull, term_ctr(CID_SCon, STAT_OFF + 810), 115ull, term_ctr(CID_SCon, STAT_OFF + 812), 101ull, term_ctr(CID_SCon, STAT_OFF + 814), 114ull, term_ctr(CID_SCon, STAT_OFF + 816), 103ull, term_ctr(CID_SCon, STAT_OFF + 818), 111ull, term_ctr(CID_SCon, STAT_OFF + 820), 114ull, term_ctr(CID_SCon, STAT_OFF + 822), 112ull, term_ctr(CID_SCon, STAT_OFF + 824), 101ull, term_ctr(CID_SCon, STAT_OFF + 480), 115ull, term_ctr(CID_SCon, STAT_OFF + 828), 97ull, term_ctr(CID_SCon, STAT_OFF + 830), 98ull, term_ctr(CID_SCon, STAT_OFF + 832), 32ull, term_ctr(CID_SCon, STAT_OFF + 834), 100ull, term_ctr(CID_SCon, STAT_OFF + 836), 97ull, term_ctr(CID_SCon, STAT_OFF + 838), 98ull, term_ctr(CID_SCon, STAT_OFF + 840), 32ull, term_ctr(CID_SCon, STAT_OFF + 842), 58ull, term_ctr(CID_SCon, STAT_OFF + 844), 120ull, term_ctr(CID_SCon, STAT_OFF + 846), 111ull, term_ctr(CID_SCon, STAT_OFF + 848), 98ull, term_ctr(CID_SCon, STAT_OFF + 850), 100ull, term_ctr(CID_SCon, STAT_OFF + 852), 110ull, term_ctr(CID_SCon, STAT_OFF + 854), 97ull, term_ctr(CID_SCon, STAT_OFF + 856), 115ull, term_ctr(CID_SCon, STAT_OFF + 858), 121ull, term_pak(CID_SNil, 0), 114ull, term_ctr(CID_SCon, STAT_OFF + 862), 114ull, term_ctr(CID_SCon, STAT_OFF + 864), 97ull, term_ctr(CID_SCon, STAT_OFF + 866), 99ull, term_ctr(CID_SCon, STAT_OFF + 868), 32ull, term_ctr(CID_SCon, STAT_OFF + 870), 100ull, term_ctr(CID_SCon, STAT_OFF + 872), 101ull, term_ctr(CID_SCon, STAT_OFF + 874), 109ull, term_ctr(CID_SCon, STAT_OFF + 876), 114ull, term_ctr(CID_SCon, STAT_OFF + 878), 111ull, term_ctr(CID_SCon, STAT_OFF + 880), 102ull, term_ctr(CID_SCon, STAT_OFF + 882), 108ull, term_ctr(CID_SCon, STAT_OFF + 884), 97ull, term_ctr(CID_SCon, STAT_OFF + 886), 109ull, term_ctr(CID_SCon, STAT_OFF + 888), 32ull, term_ctr(CID_SCon, STAT_OFF + 890), 58ull, term_ctr(CID_SCon, STAT_OFF + 892), 115ull, term_ctr(CID_SCon, STAT_OFF + 894), 101ull, term_ctr(CID_SCon, STAT_OFF + 896), 110ull, term_ctr(CID_SCon, STAT_OFF + 898), 105ull, term_ctr(CID_SCon, STAT_OFF + 900), 108ull, term_ctr(CID_SCon, STAT_OFF + 902), 95ull, term_ctr(CID_SCon, STAT_OFF + 904), 99ull, term_ctr(CID_SCon, STAT_OFF + 906), 111ull, term_ctr(CID_SCon, STAT_OFF + 908), 100ull, term_ctr(CID_SCon, STAT_OFF + 910), 110ull, term_ctr(CID_SCon, STAT_OFF + 136), 119ull, term_ctr(CID_SCon, STAT_OFF + 914), 111ull, term_ctr(CID_SCon, STAT_OFF + 916), 110ull, term_ctr(CID_SCon, STAT_OFF + 918), 107ull, term_ctr(CID_SCon, STAT_OFF + 920), 110ull, term_ctr(CID_SCon, STAT_OFF + 922), 117ull, term_ctr(CID_SCon, STAT_OFF + 924), 32ull, term_ctr(CID_SCon, STAT_OFF + 926), 58ull, term_ctr(CID_SCon, STAT_OFF + 928), 100ull, term_ctr(CID_SCon, STAT_OFF + 930), 108ull, term_ctr(CID_SCon, STAT_OFF + 932), 105ull, term_ctr(CID_SCon, STAT_OFF + 934), 104ull, term_ctr(CID_SCon, STAT_OFF + 936), 99ull, term_ctr(CID_SCon, STAT_OFF + 938), 98ull, term_ctr(CID_SCon, STAT_OFF + 810), 111ull, term_ctr(CID_SCon, STAT_OFF + 942), 106ull, term_ctr(CID_SCon, STAT_OFF + 944), 111ull, term_ctr(CID_SCon, STAT_OFF + 794), 32ull, term_ctr(CID_SCon, STAT_OFF + 948), 100ull, term_ctr(CID_SCon, STAT_OFF + 950), 101ull, term_ctr(CID_SCon, STAT_OFF + 952), 109ull, term_ctr(CID_SCon, STAT_OFF + 954), 114ull, term_ctr(CID_SCon, STAT_OFF + 956), 111ull, term_ctr(CID_SCon, STAT_OFF + 958), 102ull, term_ctr(CID_SCon, STAT_OFF + 960), 108ull, term_ctr(CID_SCon, STAT_OFF + 962), 97ull, term_ctr(CID_SCon, STAT_OFF + 964), 109ull, term_ctr(CID_SCon, STAT_OFF + 966), 32ull, term_ctr(CID_SCon, STAT_OFF + 968), 58ull, term_ctr(CID_SCon, STAT_OFF + 970), 110ull, term_ctr(CID_SCon, STAT_OFF + 972), 111ull, term_ctr(CID_SCon, STAT_OFF + 974), 105ull, term_ctr(CID_SCon, STAT_OFF + 976), 115ull, term_ctr(CID_SCon, STAT_OFF + 978), 115ull, term_ctr(CID_SCon, STAT_OFF + 980), 105ull, term_ctr(CID_SCon, STAT_OFF + 982), 109ull, term_ctr(CID_SCon, STAT_OFF + 984), 100ull, term_ctr(CID_SCon, STAT_OFF + 986), 97ull, term_ctr(CID_SCon, STAT_OFF + 988), 32ull, term_ctr(CID_SCon, STAT_OFF + 990), 69ull, term_ctr(CID_SCon, STAT_OFF + 992), 110ull, term_ctr(CID_SCon, STAT_OFF + 166), 117ull, term_ctr(CID_SCon, STAT_OFF + 996), 114ull, term_ctr(CID_SCon, STAT_OFF + 998), 32ull, term_ctr(CID_SCon, STAT_OFF + 1000), 110ull, term_ctr(CID_SCon, STAT_OFF + 1002), 101ull, term_ctr(CID_SCon, STAT_OFF + 1004), 101ull, term_ctr(CID_SCon, STAT_OFF + 1006), 115ull, term_ctr(CID_SCon, STAT_OFF + 1008), 32ull, term_ctr(CID_SCon, STAT_OFF + 1010), 100ull, term_ctr(CID_SCon, STAT_OFF + 1012), 101ull, term_ctr(CID_SCon, STAT_OFF + 1014), 109ull, term_ctr(CID_SCon, STAT_OFF + 1016), 114ull, term_ctr(CID_SCon, STAT_OFF + 1018), 111ull, term_ctr(CID_SCon, STAT_OFF + 1020), 102ull, term_ctr(CID_SCon, STAT_OFF + 1022), 108ull, term_ctr(CID_SCon, STAT_OFF + 1024), 97ull, term_ctr(CID_SCon, STAT_OFF + 1026), 109ull, term_ctr(CID_SCon, STAT_OFF + 1028), 32ull, term_ctr(CID_SCon, STAT_OFF + 1030), 58ull, term_ctr(CID_SCon, STAT_OFF + 1032), 110ull, term_ctr(CID_SCon, STAT_OFF + 1034), 101ull, term_ctr(CID_SCon, STAT_OFF + 1036), 101ull, term_ctr(CID_SCon, STAT_OFF + 1038), 115ull, term_ctr(CID_SCon, STAT_OFF + 1040), 95ull, term_ctr(CID_SCon, STAT_OFF + 1042), 99ull, term_ctr(CID_SCon, STAT_OFF + 1044), 111ull, term_ctr(CID_SCon, STAT_OFF + 1046), 100ull, term_ctr(CID_SCon, STAT_OFF + 1048), 100ull, term_ctr(CID_SCon, STAT_OFF + 136), 101ull, term_ctr(CID_SCon, STAT_OFF + 1052), 109ull, term_ctr(CID_SCon, STAT_OFF + 1054), 114ull, term_ctr(CID_SCon, STAT_OFF + 1056), 111ull, term_ctr(CID_SCon, STAT_OFF + 1058), 102ull, term_ctr(CID_SCon, STAT_OFF + 1060), 108ull, term_ctr(CID_SCon, STAT_OFF + 1062), 97ull, term_ctr(CID_SCon, STAT_OFF + 1064), 109ull, term_ctr(CID_SCon, STAT_OFF + 1066), 32ull, term_ctr(CID_SCon, STAT_OFF + 1068), 58ull, term_ctr(CID_SCon, STAT_OFF + 1070), 119ull, term_ctr(CID_SCon, STAT_OFF + 1072), 111ull, term_ctr(CID_SCon, STAT_OFF + 1074), 108ull, term_ctr(CID_SCon, STAT_OFF + 1076), 102ull, term_ctr(CID_SCon, STAT_OFF + 1078), 107ull, term_ctr(CID_SCon, STAT_OFF + 1080), 114ull, term_ctr(CID_SCon, STAT_OFF + 1082), 111ull, term_ctr(CID_SCon, STAT_OFF + 1084), 119ull, term_ctr(CID_SCon, STAT_OFF + 1086), 107ull, term_ctr(CID_SCon, STAT_OFF + 1072), 99ull, term_ctr(CID_SCon, STAT_OFF + 1090), 97ull, term_ctr(CID_SCon, STAT_OFF + 1092), 98ull, term_ctr(CID_SCon, STAT_OFF + 1094), 108ull, term_ctr(CID_SCon, STAT_OFF + 1096), 108ull, term_ctr(CID_SCon, STAT_OFF + 1098), 97ull, term_ctr(CID_SCon, STAT_OFF + 1100), 102ull, term_ctr(CID_SCon, STAT_OFF + 1102), 95ull, term_ctr(CID_SCon, STAT_OFF + 1104), 120ull, term_ctr(CID_SCon, STAT_OFF + 1106), 117ull, term_ctr(CID_SCon, STAT_OFF + 1108), 97ull, term_ctr(CID_SCon, STAT_OFF + 1110), 108ull, term_ctr(CID_SCon, STAT_OFF + 1072), 101ull, term_ctr(CID_SCon, STAT_OFF + 1114), 100ull, term_ctr(CID_SCon, STAT_OFF + 1116), 111ull, term_ctr(CID_SCon, STAT_OFF + 1118), 109ull, term_ctr(CID_SCon, STAT_OFF + 1120), 95ull, term_ctr(CID_SCon, STAT_OFF + 1122), 116ull, term_ctr(CID_SCon, STAT_OFF + 1124), 108ull, term_ctr(CID_SCon, STAT_OFF + 1126), 117ull, term_ctr(CID_SCon, STAT_OFF + 1128), 97ull, term_ctr(CID_SCon, STAT_OFF + 1130), 102ull, term_ctr(CID_SCon, STAT_OFF + 1132), 101ull, term_ctr(CID_SCon, STAT_OFF + 1134), 100ull, term_ctr(CID_SCon, STAT_OFF + 1136), 110ull, term_ctr(CID_SCon, STAT_OFF + 308), 117ull, term_ctr(CID_SCon, STAT_OFF + 1140), 111ull, term_ctr(CID_SCon, STAT_OFF + 1142), 98ull, term_ctr(CID_SCon, STAT_OFF + 1144), 32ull, term_ctr(CID_SCon, STAT_OFF + 1146), 100ull, term_ctr(CID_SCon, STAT_OFF + 1148), 97ull, term_ctr(CID_SCon, STAT_OFF + 1150), 98ull, term_ctr(CID_SCon, STAT_OFF + 1152), 32ull, term_ctr(CID_SCon, STAT_OFF + 1154), 58ull, term_ctr(CID_SCon, STAT_OFF + 1156), 115ull, term_ctr(CID_SCon, STAT_OFF + 1158), 115ull, term_ctr(CID_SCon, STAT_OFF + 1160), 101ull, term_ctr(CID_SCon, STAT_OFF + 1162), 114ull, term_ctr(CID_SCon, STAT_OFF + 1164), 103ull, term_ctr(CID_SCon, STAT_OFF + 1166), 111ull, term_ctr(CID_SCon, STAT_OFF + 1168), 114ull, term_ctr(CID_SCon, STAT_OFF + 1170), 112ull, term_ctr(CID_SCon, STAT_OFF + 1172), 116ull, term_ctr(CID_SCon, STAT_OFF + 480), 110ull, term_ctr(CID_SCon, STAT_OFF + 1176), 101ull, term_ctr(CID_SCon, STAT_OFF + 1178), 114ull, term_ctr(CID_SCon, STAT_OFF + 1180), 97ull, term_ctr(CID_SCon, STAT_OFF + 1182), 112ull, term_ctr(CID_SCon, STAT_OFF + 1184), 32ull, term_ctr(CID_SCon, STAT_OFF + 1186), 100ull, term_ctr(CID_SCon, STAT_OFF + 1188), 97ull, term_ctr(CID_SCon, STAT_OFF + 1190), 98ull, term_ctr(CID_SCon, STAT_OFF + 1192), 32ull, term_ctr(CID_SCon, STAT_OFF + 1194), 58ull, term_ctr(CID_SCon, STAT_OFF + 1196), 120ull, term_ctr(CID_SCon, STAT_OFF + 1198), 111ull, term_ctr(CID_SCon, STAT_OFF + 1200), 98ull, term_ctr(CID_SCon, STAT_OFF + 1202), 100ull, term_ctr(CID_SCon, STAT_OFF + 1204), 110ull, term_ctr(CID_SCon, STAT_OFF + 1206), 97ull, term_ctr(CID_SCon, STAT_OFF + 1208), 115ull, term_ctr(CID_SCon, STAT_OFF + 1210), 100ull, term_ctr(CID_SCon, STAT_OFF + 1002), 101ull, term_ctr(CID_SCon, STAT_OFF + 1214), 109ull, term_ctr(CID_SCon, STAT_OFF + 1216), 114ull, term_ctr(CID_SCon, STAT_OFF + 1218), 111ull, term_ctr(CID_SCon, STAT_OFF + 1220), 102ull, term_ctr(CID_SCon, STAT_OFF + 1222), 108ull, term_ctr(CID_SCon, STAT_OFF + 1224), 97ull, term_ctr(CID_SCon, STAT_OFF + 1226), 109ull, term_ctr(CID_SCon, STAT_OFF + 1228), 32ull, term_ctr(CID_SCon, STAT_OFF + 1230), 58ull, term_ctr(CID_SCon, STAT_OFF + 1232), 115ull, term_ctr(CID_SCon, STAT_OFF + 1234), 101ull, term_ctr(CID_SCon, STAT_OFF + 1236), 110ull, term_ctr(CID_SCon, STAT_OFF + 1238), 105ull, term_ctr(CID_SCon, STAT_OFF + 1240), 108ull, term_ctr(CID_SCon, STAT_OFF + 1242), 95ull, term_ctr(CID_SCon, STAT_OFF + 1244), 99ull, term_ctr(CID_SCon, STAT_OFF + 1246), 111ull, term_ctr(CID_SCon, STAT_OFF + 1248), 100ull, term_ctr(CID_SCon, STAT_OFF + 1250), 97ull, term_ctr(CID_SCon, STAT_OFF + 1052), 98ull, term_ctr(CID_SCon, STAT_OFF + 1254), 32ull, term_ctr(CID_SCon, STAT_OFF + 1256), 58ull, term_ctr(CID_SCon, STAT_OFF + 1258), 100ull, term_ctr(CID_SCon, STAT_OFF + 1260), 108ull, term_ctr(CID_SCon, STAT_OFF + 1262), 105ull, term_ctr(CID_SCon, STAT_OFF + 1264), 104ull, term_ctr(CID_SCon, STAT_OFF + 1266), 99ull, term_ctr(CID_SCon, STAT_OFF + 1268), 98ull, term_ctr(CID_SCon, STAT_OFF + 1158), 111ull, term_ctr(CID_SCon, STAT_OFF + 1272), 106ull, term_ctr(CID_SCon, STAT_OFF + 1274), 110ull, term_pak(CID_SNil, 0), 101ull, term_ctr(CID_SCon, STAT_OFF + 1278), 112ull, term_ctr(CID_SCon, STAT_OFF + 1280), 111ull, term_ctr(CID_SCon, STAT_OFF + 1282), 32ull, term_ctr(CID_SCon, STAT_OFF + 1284), 100ull, term_ctr(CID_SCon, STAT_OFF + 1286), 101ull, term_ctr(CID_SCon, STAT_OFF + 1288), 109ull, term_ctr(CID_SCon, STAT_OFF + 1290), 114ull, term_ctr(CID_SCon, STAT_OFF + 1292), 111ull, term_ctr(CID_SCon, STAT_OFF + 1294), 102ull, term_ctr(CID_SCon, STAT_OFF + 1296), 108ull, term_ctr(CID_SCon, STAT_OFF + 1298), 97ull, term_ctr(CID_SCon, STAT_OFF + 1300), 109ull, term_ctr(CID_SCon, STAT_OFF + 1302), 32ull, term_ctr(CID_SCon, STAT_OFF + 1304), 58ull, term_ctr(CID_SCon, STAT_OFF + 1306), 110ull, term_ctr(CID_SCon, STAT_OFF + 1308), 111ull, term_ctr(CID_SCon, STAT_OFF + 1310), 105ull, term_ctr(CID_SCon, STAT_OFF + 1312), 115ull, term_ctr(CID_SCon, STAT_OFF + 1314), 115ull, term_ctr(CID_SCon, STAT_OFF + 1316), 105ull, term_ctr(CID_SCon, STAT_OFF + 1318), 109ull, term_ctr(CID_SCon, STAT_OFF + 1320), 100ull, term_ctr(CID_SCon, STAT_OFF + 1322), 97ull, term_ctr(CID_SCon, STAT_OFF + 1324), 32ull, term_ctr(CID_SCon, STAT_OFF + 1326), 69ull, term_ctr(CID_SCon, STAT_OFF + 1328), 50ull, term_pak(CID_SNil, 0), 51ull, term_ctr(CID_SCon, STAT_OFF + 1332), 85ull, term_ctr(CID_SCon, STAT_OFF + 1334), 32ull, term_ctr(CID_SCon, STAT_OFF + 1336), 108ull, term_ctr(CID_SCon, STAT_OFF + 1338), 97ull, term_ctr(CID_SCon, STAT_OFF + 1340), 109ull, term_ctr(CID_SCon, STAT_OFF + 1342), 105ull, term_ctr(CID_SCon, STAT_OFF + 1344), 99ull, term_ctr(CID_SCon, STAT_OFF + 1346), 101ull, term_ctr(CID_SCon, STAT_OFF + 1348), 100ull, term_ctr(CID_SCon, STAT_OFF + 1350), 32ull, term_ctr(CID_SCon, STAT_OFF + 1352), 97ull, term_ctr(CID_SCon, STAT_OFF + 1354), 32ull, term_ctr(CID_SCon, STAT_OFF + 1356), 115ull, term_ctr(CID_SCon, STAT_OFF + 1358), 116ull, term_ctr(CID_SCon, STAT_OFF + 1360), 110ull, term_ctr(CID_SCon, STAT_OFF + 1362), 97ull, term_ctr(CID_SCon, STAT_OFF + 1364), 119ull, term_ctr(CID_SCon, STAT_OFF + 1366), 32ull, term_ctr(CID_SCon, STAT_OFF + 1368), 110ull, term_ctr(CID_SCon, STAT_OFF + 1370), 101ull, term_ctr(CID_SCon, STAT_OFF + 1372), 112ull, term_ctr(CID_SCon, STAT_OFF + 1374), 111ull, term_ctr(CID_SCon, STAT_OFF + 1376), 32ull, term_ctr(CID_SCon, STAT_OFF + 1378), 58ull, term_ctr(CID_SCon, STAT_OFF + 1380), 111ull, term_ctr(CID_SCon, STAT_OFF + 1382), 104ull, term_ctr(CID_SCon, STAT_OFF + 1384), 99ull, term_ctr(CID_SCon, STAT_OFF + 1386), 101ull, term_ctr(CID_SCon, STAT_OFF + 1388), 32ull, term_ctr(CID_SCon, STAT_OFF + 1390), 69ull, term_ctr(CID_SCon, STAT_OFF + 1392), 101ull, term_ctr(CID_SCon, STAT_OFF + 308), 115ull, term_ctr(CID_SCon, STAT_OFF + 1396), 117ull, term_ctr(CID_SCon, STAT_OFF + 1398), 102ull, term_ctr(CID_SCon, STAT_OFF + 1400), 101ull, term_ctr(CID_SCon, STAT_OFF + 1402), 114ull, term_ctr(CID_SCon, STAT_OFF + 1404), 32ull, term_ctr(CID_SCon, STAT_OFF + 1406), 115ull, term_ctr(CID_SCon, STAT_OFF + 1408), 97ull, term_ctr(CID_SCon, STAT_OFF + 1410), 119ull, term_ctr(CID_SCon, STAT_OFF + 1412), 32ull, term_ctr(CID_SCon, STAT_OFF + 1414), 110ull, term_ctr(CID_SCon, STAT_OFF + 1416), 101ull, term_ctr(CID_SCon, STAT_OFF + 1418), 112ull, term_ctr(CID_SCon, STAT_OFF + 1420), 111ull, term_ctr(CID_SCon, STAT_OFF + 1422), 32ull, term_ctr(CID_SCon, STAT_OFF + 1424), 101ull, term_ctr(CID_SCon, STAT_OFF + 1426), 104ull, term_ctr(CID_SCon, STAT_OFF + 1428), 116ull, term_ctr(CID_SCon, STAT_OFF + 1430), 32ull, term_ctr(CID_SCon, STAT_OFF + 1432), 58ull, term_ctr(CID_SCon, STAT_OFF + 1434), 110ull, term_ctr(CID_SCon, STAT_OFF + 1436), 111ull, term_ctr(CID_SCon, STAT_OFF + 1438), 105ull, term_ctr(CID_SCon, STAT_OFF + 1440), 115ull, term_ctr(CID_SCon, STAT_OFF + 1442), 115ull, term_ctr(CID_SCon, STAT_OFF + 1444), 105ull, term_ctr(CID_SCon, STAT_OFF + 1446), 109ull, term_ctr(CID_SCon, STAT_OFF + 1448), 100ull, term_ctr(CID_SCon, STAT_OFF + 1450), 97ull, term_ctr(CID_SCon, STAT_OFF + 1452), 32ull, term_ctr(CID_SCon, STAT_OFF + 1454), 69ull, term_ctr(CID_SCon, STAT_OFF + 1456), 32ull, term_pak(CID_SNil, 0), 111ull, term_ctr(CID_SCon, STAT_OFF + 1436), 104ull, term_ctr(CID_SCon, STAT_OFF + 1462), 99ull, term_ctr(CID_SCon, STAT_OFF + 1464), 101ull, term_ctr(CID_SCon, STAT_OFF + 1466), 32ull, term_ctr(CID_SCon, STAT_OFF + 1468), 69ull, term_ctr(CID_SCon, STAT_OFF + 1470), 116ull, term_ctr(CID_SCon, STAT_OFF + 864), 110ull, term_ctr(CID_SCon, STAT_OFF + 1474), 101ull, term_ctr(CID_SCon, STAT_OFF + 1476), 32ull, term_ctr(CID_SCon, STAT_OFF + 1478), 110ull, term_ctr(CID_SCon, STAT_OFF + 1480), 119ull, term_ctr(CID_SCon, STAT_OFF + 1482), 111ull, term_ctr(CID_SCon, STAT_OFF + 1484), 110ull, term_ctr(CID_SCon, STAT_OFF + 1486), 107ull, term_ctr(CID_SCon, STAT_OFF + 1488), 110ull, term_ctr(CID_SCon, STAT_OFF + 1490), 117ull, term_ctr(CID_SCon, STAT_OFF + 1492), 32ull, term_ctr(CID_SCon, STAT_OFF + 1494), 69ull, term_ctr(CID_SCon, STAT_OFF + 1496), 97ull, term_ctr(CID_SCon, STAT_OFF + 76), 99ull, term_ctr(CID_SCon, STAT_OFF + 1500), 93ull, term_pak(CID_SNil, 0), 46ull, term_ctr(CID_SCon, STAT_OFF + 1504), 46ull, term_ctr(CID_SCon, STAT_OFF + 1506), 46ull, term_ctr(CID_SCon, STAT_OFF + 1508), 62ull, term_ctr(CID_SCon, STAT_OFF + 1510), 116ull, term_ctr(CID_SCon, STAT_OFF + 1512), 110ull, term_ctr(CID_SCon, STAT_OFF + 1514), 101ull, term_ctr(CID_SCon, STAT_OFF + 1516), 118ull, term_ctr(CID_SCon, STAT_OFF + 1518), 101ull, term_ctr(CID_SCon, STAT_OFF + 1520), 60ull, term_ctr(CID_SCon, STAT_OFF + 1522), 91ull, term_ctr(CID_SCon, STAT_OFF + 1524), 32ull, term_ctr(CID_SCon, STAT_OFF + 1526), 62ull, term_ctr(CID_SCon, STAT_OFF + 1528), 116ull, term_ctr(CID_SCon, STAT_OFF + 1530), 117ull, term_ctr(CID_SCon, STAT_OFF + 1532), 112ull, term_ctr(CID_SCon, STAT_OFF + 1534), 110ull, term_ctr(CID_SCon, STAT_OFF + 1536), 105ull, term_ctr(CID_SCon, STAT_OFF + 1538), 60ull, term_ctr(CID_SCon, STAT_OFF + 1540), 32ull, term_ctr(CID_SCon, STAT_OFF + 1542), 62ull, term_ctr(CID_SCon, STAT_OFF + 1544), 121ull, term_ctr(CID_SCon, STAT_OFF + 1546), 114ull, term_ctr(CID_SCon, STAT_OFF + 1548), 116ull, term_ctr(CID_SCon, STAT_OFF + 1550), 110ull, term_ctr(CID_SCon, STAT_OFF + 1552), 101ull, term_ctr(CID_SCon, STAT_OFF + 1554), 60ull, term_ctr(CID_SCon, STAT_OFF + 1556), 32ull, term_ctr(CID_SCon, STAT_OFF + 1558), 110ull, term_ctr(CID_SCon, STAT_OFF + 1560), 101ull, term_ctr(CID_SCon, STAT_OFF + 1562), 112ull, term_ctr(CID_SCon, STAT_OFF + 1564), 111ull, term_ctr(CID_SCon, STAT_OFF + 1566), 32ull, term_ctr(CID_SCon, STAT_OFF + 1568), 101ull, term_ctr(CID_SCon, STAT_OFF + 1570), 114ull, term_ctr(CID_SCon, STAT_OFF + 1572), 111ull, term_ctr(CID_SCon, STAT_OFF + 1574), 99ull, term_ctr(CID_SCon, STAT_OFF + 1576), 32ull, term_ctr(CID_SCon, STAT_OFF + 1578), 124ull, term_ctr(CID_SCon, STAT_OFF + 1580), 32ull, term_ctr(CID_SCon, STAT_OFF + 1582), 62ull, term_ctr(CID_SCon, STAT_OFF + 1584), 116ull, term_ctr(CID_SCon, STAT_OFF + 1586), 117ull, term_ctr(CID_SCon, STAT_OFF + 1588), 112ull, term_ctr(CID_SCon, STAT_OFF + 1590), 110ull, term_ctr(CID_SCon, STAT_OFF + 1592), 105ull, term_ctr(CID_SCon, STAT_OFF + 1594), 60ull, term_ctr(CID_SCon, STAT_OFF + 1596), 32ull, term_ctr(CID_SCon, STAT_OFF + 1598), 62ull, term_ctr(CID_SCon, STAT_OFF + 1600), 121ull, term_ctr(CID_SCon, STAT_OFF + 1602), 114ull, term_ctr(CID_SCon, STAT_OFF + 1604), 116ull, term_ctr(CID_SCon, STAT_OFF + 1606), 110ull, term_ctr(CID_SCon, STAT_OFF + 1608), 101ull, term_ctr(CID_SCon, STAT_OFF + 1610), 60ull, term_ctr(CID_SCon, STAT_OFF + 1612), 32ull, term_ctr(CID_SCon, STAT_OFF + 1614), 108ull, term_ctr(CID_SCon, STAT_OFF + 1616), 108ull, term_ctr(CID_SCon, STAT_OFF + 1618), 97ull, term_ctr(CID_SCon, STAT_OFF + 1620), 99ull, term_ctr(CID_SCon, STAT_OFF + 1622), 32ull, term_ctr(CID_SCon, STAT_OFF + 1624), 101ull, term_ctr(CID_SCon, STAT_OFF + 1626), 114ull, term_ctr(CID_SCon, STAT_OFF + 1628), 111ull, term_ctr(CID_SCon, STAT_OFF + 1630), 99ull, term_ctr(CID_SCon, STAT_OFF + 1632), 32ull, term_ctr(CID_SCon, STAT_OFF + 1634), 58ull, term_ctr(CID_SCon, STAT_OFF + 1636), 101ull, term_ctr(CID_SCon, STAT_OFF + 1638), 103ull, term_ctr(CID_SCon, STAT_OFF + 1640), 97ull, term_ctr(CID_SCon, STAT_OFF + 1642), 115ull, term_ctr(CID_SCon, STAT_OFF + 1644), 117ull, term_ctr(CID_SCon, STAT_OFF + 1646) };

INLINE Term spin_1(Env e, THR Term* o, u32 r0) {
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

INLINE Term spin_0(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_1(e, _o_0, ((_a_0 > _b_0) + (_a_0 >= _b_0))) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_2(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _b_1 = r0;
  WL_SPIN
    if (_b_1 == 0) {
      o[0] = 1;
    } else {
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_3(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _c_0 = r0;
  Term _c_1 = r1;
  WL_SPIN
    o[0] = _c_0;
  break;
  }
  return 1;
}

INLINE Term spin_4(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _c_2 = r0;
  Term _c_3 = r1;
  WL_SPIN
    o[0] = _c_3;
  break;
  }
  return 1;
}

INLINE Term spin_5(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _rest_0 = r0;
  u32 _tok_0 = r1;
  Term _tok_1 = r2;
  Term _tries_0 = r3;
  WL_SPIN
    if (_rest_0 == 0) {
      o[0] = 1;
      o[1] = 3;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else {
      Term _p_0 = (_rest_0 - 1);
      o[0] = 0;
      o[1] = _tok_0;
      o[2] = _tok_1;
      o[3] = nat_chk(e, _p_0 + 1);
      o[4] = _tries_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_6(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _tok_2 = r0;
  Term _tok_3 = r1;
  Term _x_0 = r2;
  WL_SPIN
    if (_tok_2 == 0) {
      o[0] = 1;
    } else {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_0(e, _o_0, _tok_3, _x_0) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[1];
      if (spin_2(e, _o_1, _v_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_7(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  Term _cfg_2 = r0;
  Term _cfg_3 = r1;
  u32 _t_2 = r2;
  Term _t_3 = r3;
  WL_SPIN
    Term _v_4 = 0;
    Term _o_0[1];
    if (spin_3(e, _o_0, _cfg_2, _cfg_3) == 0) {
      return 0;
    }
    _v_4 = _o_0[0];
    Term _v_5 = 0;
    Term _o_1[1];
    if (spin_4(e, _o_1, _cfg_2, _cfg_3) == 0) {
      return 0;
    }
    _v_5 = _o_1[0];
    o[0] = _t_2;
    o[1] = _t_3;
    o[2] = _v_4;
    o[3] = _v_5;
  break;
  }
  return 1;
}

INLINE Term spin_8(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _w_4 = r0;
  Term _w_5 = r1;
  Term _w_6 = r2;
  Term _w_7 = r3;
  WL_SPIN
    o[0] = _w_4;
    o[1] = _w_5;
  break;
  }
  return 1;
}

INLINE Term spin_9(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _tok_0 = r0;
  Term _tok_1 = r1;
  u32 _t_0 = r2;
  Term _t_1 = r3;
  WL_SPIN
    if (_t_0 == 0) {
      o[0] = 0;
    } else {
      Term _o_4[1];
      if (spin_6(e, _o_4, _tok_0, _tok_1, _t_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_4[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_10(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4, Term r5, Term r6, u32 r7, Term r8, Term r9) {
  u32 wpoll = 0;
  u32 _news_0 = r0;
  Term _cfg_2 = r1;
  Term _cfg_3 = r2;
  u32 _w_8 = r3;
  Term _w_9 = r4;
  Term _w_10 = r5;
  Term _w_11 = r6;
  u32 _t_2 = r7;
  Term _t_3 = r8;
  Term _e_1 = r9;
  WL_SPIN
    if (_news_0 == 1) {
      u32 _v_3 = 0;
      Term _v_4 = 0;
      Term _v_5 = 0;
      Term _v_6 = 0;
      Term _o_6[4];
      if (spin_7(e, _o_6, _cfg_2, _cfg_3, _t_2, _t_3) == 0) {
        return 0;
      }
      _v_3 = (u32)_o_6[0];
      _v_4 = _o_6[1];
      _v_5 = _o_6[2];
      _v_6 = _o_6[3];
      o[0] = 0;
      o[1] = _v_3;
      o[2] = _v_4;
      o[3] = _v_5;
      o[4] = _v_6;
    } else {
      Term _v_7 = 0;
      Term _o_7[1];
      if (spin_4(e, _o_7, _cfg_2, _cfg_3) == 0) {
        return 0;
      }
      _v_7 = _o_7[0];
      Term _o_8[5];
      if (spin_5(e, _o_8, (_w_10 < _e_1 ? 0 : _w_10 - _e_1), _w_8, _w_9, _v_7) == 0) {
        return 0;
      }
      o[0] = (u32)_o_8[0];
      o[1] = (u32)_o_8[1];
      o[2] = _o_8[2];
      o[3] = _o_8[3];
      o[4] = _o_8[4];
    }
  break;
  }
  return 1;
}

INLINE Term spin_11(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _w_12 = r0;
  Term _w_13 = r1;
  Term _w_14 = r2;
  Term _w_15 = r3;
  Term _e_2 = r4;
  WL_SPIN
    if (_w_15 == 0) {
      o[0] = 1;
      o[1] = 4;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else if (_w_15 == 1) {
      o[0] = 1;
      o[1] = 4;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else {
      Term _q_0 = (_w_15 - 2);
      Term _o_10[5];
      if (spin_5(e, _o_10, (_w_14 < _e_2 ? 0 : _w_14 - _e_2), _w_12, _w_13, nat_chk(e, _q_0 + 1)) == 0) {
        return 0;
      }
      o[0] = (u32)_o_10[0];
      o[1] = (u32)_o_10[1];
      o[2] = _o_10[2];
      o[3] = _o_10[3];
      o[4] = _o_10[4];
    }
  break;
  }
  return 1;
}

INLINE Term spin_12(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _replied_0 = r0;
  WL_SPIN
    if (_replied_0 == 1) {
      o[0] = 2;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
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

INLINE Term spin_13(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _m_1 = r0;
  u32 _k_0 = r1;
  WL_SPIN
    if (_m_1 == 0) {
      o[0] = 1;
      o[1] = _k_0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else {
      o[0] = 2;
      o[1] = 1;
      o[2] = _k_0;
      o[3] = 0;
      o[4] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_14(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  u32 _r_2 = r2;
  Term _r_3 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
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

INLINE Term spin_17(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  Term _p_1 = r1;
  WL_SPIN
    o[0] = _p_0;
  break;
  }
  return 1;
}

INLINE Term spin_16(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _a_1 = (_b_0 == 0 ? 0 : _a_0 / _b_0);
    Term _a_2 = (_b_0 == 0 ? _a_0 : _a_0 % _b_0);
    Term _o_0[1];
    if (spin_17(e, _o_0, _a_1, _a_2) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_19(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_2 = r0;
  Term _p_3 = r1;
  WL_SPIN
    o[0] = _p_3;
  break;
  }
  return 1;
}

INLINE Term spin_18(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_3 = r0;
  Term _b_1 = r1;
  WL_SPIN
    Term _a_4 = (_b_1 == 0 ? 0 : _a_3 / _b_1);
    Term _a_5 = (_b_1 == 0 ? _a_3 : _a_3 % _b_1);
    Term _o_2[1];
    if (spin_19(e, _o_2, _a_4, _a_5) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_20(Env e, THR Term* o, Term r0) {
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

INLINE Term spin_21(Env e, THR Term* o, Term r0, Term r1, Term r2) {
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
        Term _m_2 = nat_chk(e, _p_5 + 1);
        Term _v_3 = 0;
        Term _o_5[1];
        if (spin_16(e, _o_5, _m_2, 10ull) == 0) {
          return 0;
        }
        _v_3 = _o_5[0];
        u32 _v_4 = 0;
        Term _v_5 = 0;
        Term _o_6[1];
        if (spin_18(e, _o_6, _m_2, 10ull) == 0) {
          return 0;
        }
        _v_5 = _o_6[0];
        Term _o_7[1];
        if (spin_20(e, _o_7, _v_5) == 0) {
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
        WL_AGAIN(spin_21);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_15(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_1[1];
    if (spin_16(e, _o_1, _n_0, 10ull) == 0) {
      return 0;
    }
    _v_0 = _o_1[0];
    u32 _v_1 = 0;
    Term _v_2 = 0;
    Term _o_3[1];
    if (spin_18(e, _o_3, _n_0, 10ull) == 0) {
      return 0;
    }
    _v_2 = _o_3[0];
    Term _o_4[1];
    if (spin_20(e, _o_4, _v_2) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_4[0];
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, 44ull);
    e.mem[_nd_0 + 1] = rfc_seal(e, _rest_1);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _v_1);
    e.mem[_nd_1 + 1] = rfc_seal(e, term_ctr(CID_SCon, _nd_0));
    Term _o_8[1];
    if (spin_21(e, _o_8, _n_0, _v_0, term_ctr(CID_SCon, _nd_1)) == 0) {
      return 0;
    }
    o[0] = _o_8[0];
  break;
  }
  return 1;
}

INLINE Term spin_22(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  u32 _r_4 = r1;
  u32 _r_5 = r2;
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

INLINE Term spin_23(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _p_2 = r0;
  Term _s_0 = r1;
  u32 _d_4 = r2;
  Term _d_5 = r3;
  Term _d_6 = r4;
  WL_SPIN
    if (_d_4 == 0) {
      o[0] = 0;
      o[1] = _p_2;
      o[2] = _s_0;
      o[3] = _d_5;
      o[4] = _d_6;
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

INLINE Term spin_24(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4, Term r5, Term r6, u32 r7, u32 r8, Term r9) {
  u32 wpoll = 0;
  Term _cfg_2 = r0;
  Term _cfg_3 = r1;
  u32 _w_4 = r2;
  Term _w_5 = r3;
  Term _w_6 = r4;
  Term _w_7 = r5;
  Term _e_1 = r6;
  u32 _o_3 = r7;
  u32 _o_4 = r8;
  Term _o_5 = r9;
  WL_SPIN
    if (_o_3 == 0) {
      u32 _v_5 = 0;
      u32 _v_6 = 0;
      Term _v_7 = 0;
      Term _o_6[2];
      if (spin_8(e, _o_6, _w_4, _w_5, _w_6, _w_7) == 0) {
        return 0;
      }
      _v_6 = (u32)_o_6[0];
      _v_7 = _o_6[1];
      Term _o_7[1];
      if (spin_9(e, _o_7, _v_6, _v_7, _o_4, _o_5) == 0) {
        return 0;
      }
      _v_5 = (u32)_o_7[0];
      Term _o_8[5];
      if (spin_10(e, _o_8, _v_5, _cfg_2, _cfg_3, _w_4, _w_5, _w_6, _w_7, _o_4, _o_5, _e_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_8[0];
      o[1] = (u32)_o_8[1];
      o[2] = _o_8[2];
      o[3] = _o_8[3];
      o[4] = _o_8[4];
    } else if (_o_3 == 1) {
      Term _o_9[5];
      if (spin_11(e, _o_9, _w_4, _w_5, _w_6, _w_7, _e_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_9[0];
      o[1] = (u32)_o_9[1];
      o[2] = _o_9[2];
      o[3] = _o_9[3];
      o[4] = _o_9[4];
    } else if (_o_3 == 2) {
      Term _o_10[5];
      if (spin_12(e, _o_10, _o_4) == 0) {
        return 0;
      }
      o[0] = (u32)_o_10[0];
      o[1] = (u32)_o_10[1];
      o[2] = _o_10[2];
      o[3] = _o_10[3];
      o[4] = _o_10[4];
    } else if (_o_3 == 3) {
      o[0] = 1;
      o[1] = 1;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else {
      o[0] = 1;
      o[1] = 1;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_25(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, u32 r5) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  u32 _x_1 = r1;
  Term _x_2 = r2;
  Term _x_3 = r3;
  Term _x_4 = r4;
  u32 _m_1 = r5;
  WL_SPIN
    if (_x_0 == 0) {
      o[0] = 0;
      o[1] = _x_1;
      o[2] = _x_2;
      o[3] = _x_3;
      o[4] = _x_4;
    } else if (_x_0 == 1) {
      Term _o_12[5];
      if (spin_13(e, _o_12, _m_1, _x_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_12[0];
      o[1] = (u32)_o_12[1];
      o[2] = _o_12[2];
      o[3] = _o_12[3];
      o[4] = _o_12[4];
    } else {
      o[0] = 2;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_27(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  Term _rest_2 = r2;
  WL_SPIN
    if (_m_0 == 0) {
      Term _o_2[1];
      if (spin_15(e, _o_2, 0, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _v_3 = 0;
      Term _o_3[1];
      if (spin_15(e, _o_3, _m_1, _rest_2) == 0) {
        return 0;
      }
      _v_3 = _o_3[0];
      Term _o_4[1];
      if (spin_15(e, _o_4, 1ull, _v_3) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_26(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _w_0 = r0;
  Term _w_1 = r1;
  Term _w_2 = r2;
  Term _w_3 = r3;
  Term _rest_1 = r4;
  WL_SPIN
    Term _v_1 = 0;
    Term _v_2 = 0;
    Term _o_0[1];
    if (spin_15(e, _o_0, _w_3, _rest_1) == 0) {
      return 0;
    }
    _v_2 = _o_0[0];
    Term _o_1[1];
    if (spin_15(e, _o_1, _w_2, _v_2) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    Term _o_5[1];
    if (spin_27(e, _o_5, _w_0, _w_1, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_5[0];
  break;
  }
  return 1;
}

INLINE Term spin_28(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _k_0 = r0;
  Term _rest_3 = r1;
  WL_SPIN
    if (_k_0 == 0) {
      Term _o_8[1];
      if (spin_15(e, _o_8, 0, _rest_3) == 0) {
        return 0;
      }
      o[0] = _o_8[0];
    } else if (_k_0 == 1) {
      Term _o_9[1];
      if (spin_15(e, _o_9, 1ull, _rest_3) == 0) {
        return 0;
      }
      o[0] = _o_9[0];
    } else if (_k_0 == 2) {
      Term _o_10[1];
      if (spin_15(e, _o_10, 2ull, _rest_3) == 0) {
        return 0;
      }
      o[0] = _o_10[0];
    } else if (_k_0 == 3) {
      Term _o_11[1];
      if (spin_15(e, _o_11, 3ull, _rest_3) == 0) {
        return 0;
      }
      o[0] = _o_11[0];
    } else {
      Term _o_12[1];
      if (spin_15(e, _o_12, 4ull, _rest_3) == 0) {
        return 0;
      }
      o[0] = _o_12[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_31(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _x_3 = r0;
  Term _rest_2 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_15(e, _o_0, ((u64)_x_3), _rest_2) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_30(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  u32 _c_1 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    Term _v_2 = 0;
    Term _o_1[1];
    if (spin_31(e, _o_1, _c_1, _rest_1) == 0) {
      return 0;
    }
    _v_2 = _o_1[0];
    Term _o_2[1];
    if (spin_31(e, _o_2, _c_0, _v_2) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_29(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _e_0 = r0;
  u32 _e_1 = r1;
  u32 _e_2 = r2;
  Term _rest_0 = r3;
  WL_SPIN
    if (_e_0 == 0) {
      Term _v_1 = 0;
      Term _o_3[1];
      if (spin_30(e, _o_3, _e_1, _e_2, _rest_0) == 0) {
        return 0;
      }
      _v_1 = _o_3[0];
      Term _o_4[1];
      if (spin_15(e, _o_4, 0, _v_1) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    } else {
      Term _o_5[1];
      if (spin_15(e, _o_5, 1ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_33(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  WL_SPIN
    if (_c_0 == 2) {
      o[0] = 0;
    } else {
      o[0] = 1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_32(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_33(e, _o_0, ((_a_0 > _b_0) + (_a_0 >= _b_0))) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_34(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _a_1 = r0;
  u32 _b_1 = r1;
  WL_SPIN
    if (_a_1 == 0) {
      o[0] = 0;
    } else {
      o[0] = _b_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_35(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    if (_m_0 == 0) {
      Term _o_0[1];
      if (spin_15(e, _o_0, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else {
      Term _v_1 = 0;
      Term _o_1[1];
      if (spin_15(e, _o_1, _m_1, _rest_1) == 0) {
        return 0;
      }
      _v_1 = _o_1[0];
      Term _o_2[1];
      if (spin_15(e, _o_2, 1ull, _v_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_36(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _s_0 = r1;
  WL_SPIN
    if (_n_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_0;
    } else if (_n_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_0;
    } else if (_n_0 == 2) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _s_0;
    } else if (_n_0 == 3) {
      o[0] = 0;
      o[1] = 3;
      o[2] = _s_0;
    } else if (_n_0 == 4) {
      o[0] = 0;
      o[1] = 4;
      o[2] = _s_0;
    } else if (_n_0 == 5) {
      o[0] = 0;
      o[1] = 5;
      o[2] = _s_0;
    } else {
      Term _f_0 = (_n_0 - 6);
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_37(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  u32 _x_1 = r1;
  u32 _r_0 = r2;
  Term _r_1 = r3;
  Term _r_2 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_workflow_Row, _nd_2));
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

INLINE Term spin_38(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _t_2 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _t_2;
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

INLINE Term spin_39(Env e, THR Term* o, Term r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  Term _k_1 = r1;
  Term _k_2 = r2;
  Term _rest_1 = r3;
  WL_SPIN
    Term _v_1 = 0;
    Term _v_2 = 0;
    Term _o_2[1];
    if (spin_15(e, _o_2, _k_2, _rest_1) == 0) {
      return 0;
    }
    _v_2 = _o_2[0];
    Term _o_3[1];
    if (spin_15(e, _o_3, _k_1, _v_2) == 0) {
      return 0;
    }
    _v_1 = _o_3[0];
    Term _o_4[1];
    if (spin_15(e, _o_4, _k_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_4[0];
  break;
  }
  return 1;
}

INLINE Term spin_40(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_41(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _stop_0 = r0;
  Term _n_0 = r1;
  WL_SPIN
    if (_stop_0 == 1) {
      o[0] = 1;
      o[1] = _n_0;
    } else {
      o[0] = 0;
      o[1] = _n_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_42(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
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

INLINE Term spin_45(Env e, THR Term* o, u32 r0, Term r1) {
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

INLINE Term spin_44(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
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
      if (spin_45(e, _o_1, _f_2, _s_2) == 0) {
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

INLINE Term spin_43(Env e, THR Term* o, Term r0) {
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
      if (spin_44(e, _o_2, U32_BIN(_f_0, ==, 84ull), U32_BIN(_f_0, ==, 70ull), _f_1) == 0) {
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

INLINE Term spin_46(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_4 = r0;
  u32 _r_5 = r1;
  Term _r_6 = r2;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _r_5;
      o[3] = 0;
      o[4] = _r_6;
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

INLINE Term spin_47(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  WL_SPIN
    if (_n_0 == 0) {
      o[0] = 0;
    } else if (_n_0 == 1) {
      o[0] = 1;
    } else if (_n_0 == 2) {
      o[0] = 2;
    } else if (_n_0 == 3) {
      o[0] = 3;
    } else if (_n_0 == 4) {
      o[0] = 4;
    } else {
      Term _e_0 = (_n_0 - 5);
      o[0] = 5;
    }
  break;
  }
  return 1;
}

INLINE Term spin_48(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _t_0 = r0;
  Term _s_0 = r1;
  WL_SPIN
    if (_t_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_0;
    } else if (_t_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_0;
    } else if (_t_0 == 2) {
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    } else if (_t_0 == 3) {
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    } else if (_t_0 == 4) {
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
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

INLINE Term spin_49(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4, Term r5, Term r6, u32 r7, u32 r8, Term r9, u32 r10) {
  u32 wpoll = 0;
  Term _cfg_0 = r0;
  Term _cfg_1 = r1;
  u32 _w_4 = r2;
  Term _w_5 = r3;
  Term _w_6 = r4;
  Term _w_7 = r5;
  Term _e_1 = r6;
  u32 _o_3 = r7;
  u32 _o_4 = r8;
  Term _o_5 = r9;
  u32 _m_1 = r10;
  WL_SPIN
    u32 _v_5 = 0;
    u32 _v_6 = 0;
    Term _v_7 = 0;
    Term _v_8 = 0;
    Term _v_9 = 0;
    Term _o_6[5];
    if (spin_24(e, _o_6, _cfg_0, _cfg_1, _w_4, _w_5, _w_6, _w_7, _e_1, _o_3, _o_4, _o_5) == 0) {
      return 0;
    }
    _v_5 = (u32)_o_6[0];
    _v_6 = (u32)_o_6[1];
    _v_7 = _o_6[2];
    _v_8 = _o_6[3];
    _v_9 = _o_6[4];
    Term _o_7[5];
    if (spin_25(e, _o_7, _v_5, _v_6, _v_7, _v_8, _v_9, _m_1) == 0) {
      return 0;
    }
    o[0] = (u32)_o_7[0];
    o[1] = (u32)_o_7[1];
    o[2] = _o_7[2];
    o[3] = _o_7[3];
    o[4] = _o_7[4];
  break;
  }
  return 1;
}

INLINE Term spin_50(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _c_2 = r0;
  u32 _c_3 = r1;
  Term _c_4 = r2;
  Term _c_5 = r3;
  Term _c_6 = r4;
  Term _rest_0 = r5;
  WL_SPIN
    if (_c_2 == 0) {
      Term _v_10 = 0;
      Term _o_9[1];
      if (spin_26(e, _o_9, _c_3, _c_4, _c_5, _c_6, _rest_0) == 0) {
        return 0;
      }
      _v_10 = _o_9[0];
      Term _o_10[1];
      if (spin_15(e, _o_10, 0, _v_10) == 0) {
        return 0;
      }
      o[0] = _o_10[0];
    } else if (_c_2 == 1) {
      Term _v_11 = 0;
      Term _o_11[1];
      if (spin_28(e, _o_11, _c_3, _rest_0) == 0) {
        return 0;
      }
      _v_11 = _o_11[0];
      Term _o_12[1];
      if (spin_15(e, _o_12, 1ull, _v_11) == 0) {
        return 0;
      }
      o[0] = _o_12[0];
    } else {
      if (_c_3 == 0) {
        Term _v_12 = 0;
        Term _o_13[1];
        if (spin_15(e, _o_13, 0, _rest_0) == 0) {
          return 0;
        }
        _v_12 = _o_13[0];
        Term _o_14[1];
        if (spin_15(e, _o_14, 2ull, _v_12) == 0) {
          return 0;
        }
        o[0] = _o_14[0];
      } else {
        Term _v_13 = 0;
        Term _v_14 = 0;
        Term _o_15[1];
        if (spin_28(e, _o_15, _c_4, _rest_0) == 0) {
          return 0;
        }
        _v_14 = _o_15[0];
        Term _o_16[1];
        if (spin_15(e, _o_16, 1ull, _v_14) == 0) {
          return 0;
        }
        _v_13 = _o_16[0];
        Term _o_17[1];
        if (spin_15(e, _o_17, 2ull, _v_13) == 0) {
          return 0;
        }
        o[0] = _o_17[0];
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_51(Env e, THR Term* o, Term r0) {
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

INLINE Term spin_52(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _hi_0 = r0;
  u32 _r_4 = r1;
  u32 _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _hi_0;
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

INLINE Term spin_53(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _cap_2 = r0;
  Term _cap_3 = r1;
  Term _kept_0 = r2;
  Term _n_1 = r3;
  WL_SPIN
    if (_cap_2 == 0) {
      o[0] = _n_1;
    } else {
      Term _a_0 = (_cap_3 < _kept_0 ? 0 : _cap_3 - _kept_0);
      o[0] = (_n_1 < _a_0 ? _n_1 : _a_0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_54(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  u32 _x_1 = r1;
  u32 _x_2 = r2;
  Term _r_0 = r3;
  Term _r_1 = r4;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_6[1];
    if (spin_29(e, _o_6, _x_0, _x_1, _x_2, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_6[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_55(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _s_0 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    if (_s_0 == 0) {
      Term _o_0[1];
      if (spin_15(e, _o_0, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else if (_s_0 == 1) {
      Term _o_1[1];
      if (spin_15(e, _o_1, 1ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else if (_s_0 == 2) {
      Term _o_2[1];
      if (spin_15(e, _o_2, 2ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else if (_s_0 == 3) {
      Term _o_3[1];
      if (spin_15(e, _o_3, 3ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    } else {
      Term _o_4[1];
      if (spin_15(e, _o_4, 4ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_56(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _c_0 = r0;
  Term _rest_2 = r1;
  WL_SPIN
    if (_c_0 == 0) {
      Term _o_6[1];
      if (spin_15(e, _o_6, 0, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    } else {
      Term _o_7[1];
      if (spin_15(e, _o_7, 1ull, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_7[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_57(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _m_1 = r0;
  u32 _s_0 = r1;
  WL_SPIN
    if (_m_1 == 0) {
      if (_s_0 == 0) {
        o[0] = 0;
      } else if (_s_0 == 1) {
        o[0] = 1;
      } else if (_s_0 == 2) {
        o[0] = 1;
      } else if (_s_0 == 3) {
        o[0] = 0;
      } else {
        o[0] = 0;
      }
    } else {
      if (_s_0 == 0) {
        o[0] = 1;
      } else if (_s_0 == 1) {
        o[0] = 0;
      } else if (_s_0 == 2) {
        o[0] = 0;
      } else if (_s_0 == 3) {
        o[0] = 0;
      } else {
        o[0] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_58(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _a_0 = r0;
  u32 _b_0 = r1;
  WL_SPIN
    if (_a_0 == 0) {
      if (_b_0 == 0) {
        o[0] = 1;
      } else {
        o[0] = 0;
      }
    } else {
      if (_b_0 == 0) {
        o[0] = 0;
      } else {
        o[0] = 1;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_59(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_3 = r0;
  Term _r_4 = r1;
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

INLINE Term spin_60(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _n_1 = r0;
  Term _iv_0 = r1;
  Term _iv_1 = r2;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_32(e, _o_0, _iv_0, _n_1) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    u32 _v_2 = 0;
    Term _o_1[1];
    if (spin_32(e, _o_1, _n_1, _iv_1) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_1[0];
    Term _o_2[1];
    if (spin_34(e, _o_2, _v_1, _v_2) == 0) {
      return 0;
    }
    o[0] = (u32)_o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_61(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _w_0 = r0;
  Term _w_1 = r1;
  WL_SPIN
    if (_w_0 == 0) {
      o[0] = 0;
    } else {
      Term _o_0[1];
      if (spin_32(e, _o_0, _w_1, ((u64)512ull)) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_62(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _whole_0 = r0;
  WL_SPIN
    if (_whole_0 == 1) {
      o[0] = 0;
      o[1] = 0;
    } else {
      o[0] = 1;
      o[1] = ((u64)512ull);
    }
  break;
  }
  return 1;
}

INLINE Term spin_63(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _x_3 = r0;
  u32 _x_4 = r1;
  Term _x_5 = r2;
  Term _rest_0 = r3;
  WL_SPIN
    Term _v_1 = 0;
    Term _o_0[1];
    if (spin_35(e, _o_0, _x_4, _x_5, _rest_0) == 0) {
      return 0;
    }
    _v_1 = _o_0[0];
    Term _o_1[1];
    if (spin_15(e, _o_1, _x_3, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_64(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      Term _o_0[3];
      if (spin_36(e, _o_0, _r_1, _r_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = (u32)_o_0[1];
      o[2] = _o_0[2];
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_65(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, Term r5) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  Term _x_2 = r2;
  u32 _r_0 = r3;
  Term _r_1 = r4;
  Term _r_2 = r5;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      e.mem[_nd_2 + 2] = rfc_seal(e, _x_2);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_aux_fallback_K, _nd_2));
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

INLINE Term spin_66(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  u32 _d_4 = r1;
  Term _d_5 = r2;
  Term _d_6 = r3;
  WL_SPIN
    if (_d_4 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _p_0;
      o[3] = _d_5;
      o[4] = 0;
      o[5] = 0;
      o[6] = _d_6;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_67(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _d_0 = r0;
  Term _d_1 = r1;
  Term _d_2 = r2;
  WL_SPIN
    if (_d_0 == 0) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _d_1;
      o[3] = _d_2;
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

INLINE Term spin_68(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _e_0 = r0;
  Term _e_1 = r1;
  Term _e_2 = r2;
  Term _e_3 = r3;
  Term _rest_0 = r4;
  WL_SPIN
    if (_e_0 == 0) {
      Term _o_0[1];
      if (spin_15(e, _o_0, 0, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else if (_e_0 == 1) {
      Term _o_1[1];
      if (spin_15(e, _o_1, 1ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else if (_e_0 == 2) {
      Term _v_1 = 0;
      Term _o_2[1];
      if (spin_39(e, _o_2, _e_1, _e_2, _e_3, _rest_0) == 0) {
        return 0;
      }
      _v_1 = _o_2[0];
      Term _o_3[1];
      if (spin_15(e, _o_3, 2ull, _v_1) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    } else {
      Term _v_2 = 0;
      Term _o_4[1];
      if (spin_39(e, _o_4, _e_1, _e_2, _e_3, _rest_0) == 0) {
        return 0;
      }
      _v_2 = _o_4[0];
      Term _o_5[1];
      if (spin_15(e, _o_5, 3ull, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_69(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _cap_1 = r0;
  Term _s_1 = r1;
  WL_SPIN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_32(e, _o_0, _cap_1, nat_chk(e, _s_1 + 1)) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    Term _o_1[2];
    if (spin_41(e, _o_1, _v_0, nat_chk(e, _s_1 + 1)) == 0) {
      return 0;
    }
    o[0] = (u32)_o_1[0];
    o[1] = _o_1[1];
  break;
  }
  return 1;
}

INLINE Term spin_70(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
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

INLINE Term spin_71(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
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

INLINE Term spin_72(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _e_0 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    if (_e_0 == 0) {
      Term _o_1[1];
      if (spin_15(e, _o_1, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_15(e, _o_2, 1ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_73(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _t_0 = r0;
  Term _s_0 = r1;
  WL_SPIN
    if (_t_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_0;
    } else if (_t_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_0;
    } else if (_t_0 == 2) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _s_0;
    } else if (_t_0 == 3) {
      o[0] = 0;
      o[1] = 3;
      o[2] = _s_0;
    } else if (_t_0 == 4) {
      o[0] = 0;
      o[1] = 4;
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

INLINE Term spin_74(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _t_0 = r0;
  Term _s_0 = r1;
  WL_SPIN
    if (_t_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_0;
    } else if (_t_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_0;
    } else if (_t_0 == 2) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _s_0;
    } else if (_t_0 == 3) {
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    } else if (_t_0 == 4) {
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
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

INLINE Term spin_75(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_76(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _r_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[3];
      if (spin_48(e, _o_1, _v_0, _r_2) == 0) {
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

INLINE Term spin_78(Env e, THR Term* o, Term r0) {
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

INLINE Term spin_77(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _s_0 = r0;
  WL_SPIN
    Term _o_3[1];
    if (spin_78(e, _o_3, _s_0) == 0) {
      return 0;
    }
    o[0] = (u32)_o_3[0];
  break;
  }
  return 1;
}

INLINE Term spin_79(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4, Term r5, Term r6, Term r7, u32 r8, u32 r9, Term r10, u32 r11) {
  u32 wpoll = 0;
  u32 _left_0 = r0;
  Term _c_2 = r1;
  Term _c_3 = r2;
  u32 _w_4 = r3;
  Term _w_5 = r4;
  Term _w_6 = r5;
  Term _w_7 = r6;
  Term _e_1 = r7;
  u32 _o_5 = r8;
  u32 _o_6 = r9;
  Term _o_7 = r10;
  u32 _m_0 = r11;
  WL_SPIN
    if (_left_0 == 1) {
      u32 _v_1 = 0;
      u32 _v_2 = 0;
      Term _v_3 = 0;
      Term _v_4 = 0;
      Term _v_5 = 0;
      Term _o_8[5];
      if (spin_49(e, _o_8, _c_2, _c_3, _w_4, _w_5, _w_6, _w_7, _e_1, _o_5, _o_6, _o_7, _m_0) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_8[0];
      _v_2 = (u32)_o_8[1];
      _v_3 = _o_8[2];
      _v_4 = _o_8[3];
      _v_5 = _o_8[4];
      Term _o_9[1];
      if (spin_50(e, _o_9, _v_1, _v_2, _v_3, _v_4, _v_5, term_pak(CID_SNil, 0)) == 0) {
        return 0;
      }
      o[0] = _o_9[0];
    } else {
      Term _o_10[1];
      if (spin_51(e, _o_10, term_ctr(CID_SCon, STAT_OFF + 42)) == 0) {
        return 0;
      }
      o[0] = _o_10[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_80(Env e, THR Term* o, Term r0, Term r1, u32 r2, u32 r3, u32 r4, u32 r5, Term r6) {
  u32 wpoll = 0;
  Term _k_2 = r0;
  Term _d_0 = r1;
  u32 _r_4 = r2;
  u32 _r_5 = r3;
  u32 _r_6 = r4;
  u32 _r_7 = r5;
  Term _r_8 = r6;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _k_2;
      o[3] = _d_0;
      o[4] = _r_5;
      o[5] = _r_6;
      o[6] = _r_7;
      o[7] = _r_8;
    } else {
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

INLINE Term spin_81(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _cap_2 = r0;
  Term _cap_3 = r1;
  Term _k_0 = r2;
  Term _d_0 = r3;
  Term _n_0 = r4;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_53(e, _o_0, _cap_2, _cap_3, _k_0, _n_0) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = 0;
    o[1] = nat_chk(e, _k_0 + _v_0);
    o[2] = nat_chk(e, _d_0 + (_n_0 < _v_0 ? 0 : _n_0 - _v_0));
    o[3] = 0;
    o[4] = 0;
    o[5] = 0;
  break;
  }
  return 1;
}

INLINE Term spin_82(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _r_0 = r0;
  Term _r_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_15(e, _o_0, _r_0, _r_1) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_83(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  Term _t_0 = r0;
  u32 _t_1 = r1;
  u32 _t_2 = r2;
  Term _rest_0 = r3;
  WL_SPIN
    Term _v_1 = 0;
    Term _v_2 = 0;
    Term _o_0[1];
    if (spin_55(e, _o_0, _t_2, _rest_0) == 0) {
      return 0;
    }
    _v_2 = _o_0[0];
    Term _o_1[1];
    if (spin_56(e, _o_1, _t_1, _v_2) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    Term _o_2[1];
    if (spin_15(e, _o_2, _t_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_85(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, u32 r3) {
  u32 wpoll = 0;
  u32 _m_1 = r0;
  u32 _c_3 = r1;
  u32 _t_4 = r2;
  u32 _t_5 = r3;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_57(e, _o_0, _m_1, _t_5) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    u32 _v_2 = 0;
    Term _o_1[1];
    if (spin_58(e, _o_1, _c_3, _t_4) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_1[0];
    Term _o_2[1];
    if (spin_34(e, _o_2, _v_1, _v_2) == 0) {
      return 0;
    }
    o[0] = (u32)_o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_84(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, u32 r4) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  u32 _c_2 = r1;
  Term _t_1 = r2;
  u32 _t_2 = r3;
  u32 _t_3 = r4;
  WL_SPIN
    Term _o_3[1];
    if (spin_85(e, _o_3, _m_0, _c_2, _t_2, _t_3) == 0) {
      return 0;
    }
    o[0] = (u32)_o_3[0];
  break;
  }
  return 1;
}

INLINE Term spin_86(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, u32 r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  u32 _c_4 = r1;
  Term _h_1 = r2;
  u32 _h_2 = r3;
  u32 _h_3 = r4;
  Term _r_0 = r5;
  Term _m_2 = r6;
  WL_SPIN
    if (_b_0 == 1) {
      term_sink(e, _m_2);
      u64 _nd_0 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_0 + 0] = rfc_seal(e, _h_1);
      e.mem[_nd_0 + 1] = rfc_seal(e, _c_4);
      e.mem[_nd_0 + 2] = rfc_seal(e, 1);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _r_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    } else {
      term_sink(e, _r_0);
      u64 _nd_2 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_2 + 0] = rfc_seal(e, _h_1);
      e.mem[_nd_2 + 1] = rfc_seal(e, _h_2);
      e.mem[_nd_2 + 2] = rfc_seal(e, _h_3);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, _m_2);
      o[0] = term_ctr(CID_Con, _nd_3);
    }
  break;
  }
  return 1;
}

INLINE Term spin_87(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _t_3 = r0;
  u32 _t_4 = r1;
  WL_SPIN
    if (_t_3 == 0) {
      o[0] = 0;
      o[1] = _t_4;
    } else {
      if (_t_4 == 0) {
        o[0] = 1;
        o[1] = 0;
      } else if (_t_4 == 1) {
        o[0] = 1;
        o[1] = 0;
      } else if (_t_4 == 2) {
        o[0] = 1;
        o[1] = 3;
      } else if (_t_4 == 3) {
        o[0] = 1;
        o[1] = 3;
      } else {
        o[0] = 1;
        o[1] = 4;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_88(Env e, THR Term* o, Term r0, u32 r1, u32 r2) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  u32 _t_5 = r1;
  u32 _t_6 = r2;
  WL_SPIN
    o[0] = _k_0;
    o[1] = _t_5;
    o[2] = _t_6;
  break;
  }
  return 1;
}

INLINE Term spin_89(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _ivs_1 = r0;
  Term _n_1 = r1;
  u32 _hit_0 = r2;
  WL_SPIN
    if (term_aux(_ivs_1) == CID_Nil) {
      o[0] = _hit_0;
    } else {
      u64 _sp_0 = term_peek(e.mem, _ivs_1);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      Term _f_3 = e.mem[_sp_1 + 1];
      if (_hit_0 == 1) {
        o[0] = 1;
      } else {
        u32 _v_0 = 0;
        Term _o_0[1];
        if (spin_60(e, _o_0, _n_1, _f_2, _f_3) == 0) {
          return 0;
        }
        _v_0 = (u32)_o_0[0];
        r0 = _f_1;
        r1 = _n_1;
        r2 = _v_0;
        _ivs_1 = r0;
        _n_1 = r1;
        _hit_0 = r2;
        WL_AGAIN(spin_89);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_90(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  u32 _w_0 = r1;
  Term _w_1 = r2;
  Term _rest_0 = r3;
  WL_SPIN
    if (_w_0 == 0) {
      o[0] = _rest_0;
    } else {
      u32 _v_0 = 0;
      Term _v_1 = 0;
      u32 _v_2 = 0;
      Term _o_0[1];
      if (spin_32(e, _o_0, _w_1, ((u64)512ull)) == 0) {
        return 0;
      }
      _v_2 = (u32)_o_0[0];
      Term _o_1[2];
      if (spin_62(e, _o_1, _v_2) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_1[0];
      _v_1 = _o_1[1];
      u64 _nd_0 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_0 + 0] = rfc_seal(e, _n_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _v_0);
      e.mem[_nd_0 + 2] = rfc_seal(e, _v_1);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_doc_seen_Show, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _rest_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_91(Env e, THR Term* o, Term r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  u32 _a_1 = r1;
  Term _a_2 = r2;
  WL_SPIN
    o[0] = _a_0;
  break;
  }
  return 1;
}

INLINE Term spin_92(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  u32 _x_1 = r1;
  Term _x_2 = r2;
  Term _r_0 = r3;
  Term _r_1 = r4;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_63(e, _o_0, _x_0, _x_1, _x_2, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_93(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _r_0 = r1;
  Term _r_1 = r2;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_15(e, _o_0, _x_0, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_94(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_95(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, u32 r4, Term r5, Term r6, Term r7) {
  u32 wpoll = 0;
  u32 _prior_4 = r0;
  u32 _prior_5 = r1;
  Term _k_2 = r2;
  Term _rows_0 = r3;
  u32 _r_4 = r4;
  Term _r_5 = r5;
  Term _r_6 = r6;
  Term _r_7 = r7;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _prior_4;
      o[3] = _prior_5;
      o[4] = _k_2;
      o[5] = _rows_0;
      o[6] = _r_5;
      o[7] = _r_6;
      o[8] = _r_7;
    } else {
      term_sink(e, _rows_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
      o[7] = 0;
      o[8] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_96(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_2 = r0;
  Term _p_3 = r1;
  WL_SPIN
    if (_p_3 == 0) {
      o[0] = _p_2;
      o[1] = 0;
    } else {
      Term _m_0 = (_p_3 - 1);
      o[0] = nat_chk(e, _p_2 + 1);
      o[1] = _m_0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_97(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _d_0 = r0;
  Term _d_1 = r1;
  Term _d_2 = r2;
  Term _d_3 = r3;
  Term _d_4 = r4;
  WL_SPIN
    if (_d_0 == 0) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _d_1;
      o[3] = _d_2;
      o[4] = _d_3;
      o[5] = _d_4;
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

INLINE Term spin_98(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _d_0 = r0;
  u32 _d_1 = r1;
  Term _d_2 = r2;
  Term _d_3 = r3;
  Term _d_4 = r4;
  Term _d_5 = r5;
  WL_SPIN
    if (_d_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _d_1;
      o[3] = _d_2;
      o[4] = _d_3;
      o[5] = _d_4;
      o[6] = _d_5;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_99(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _d_3 = r0;
  Term _d_4 = r1;
  Term _d_5 = r2;
  Term _n_0 = r3;
  WL_SPIN
    if (_d_3 == 0) {
      if (_n_0 == 0) {
        o[0] = 0;
        o[1] = 0;
        o[2] = _d_4;
        o[3] = _d_5;
      } else {
        Term _a_0 = (_n_0 - 1);
        o[0] = 0;
        o[1] = 1;
        o[2] = _d_4;
        o[3] = _d_5;
      }
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

INLINE Term spin_100(Env e, THR Term* o, Term r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  Term _x_1 = r1;
  Term _x_2 = r2;
  Term _r_0 = r3;
  Term _r_1 = r4;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_39(e, _o_0, _x_0, _x_1, _x_2, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_101(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  Term _x_1 = r1;
  Term _x_2 = r2;
  Term _x_3 = r3;
  Term _r_0 = r4;
  Term _r_1 = r5;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_8[1];
    if (spin_68(e, _o_8, _x_0, _x_1, _x_2, _x_3, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_8[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_102(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  u32 _k_1 = r1;
  u32 _next_2 = r2;
  Term _next_3 = r3;
  WL_SPIN
    if (_next_2 == 0) {
      o[0] = 2;
      o[1] = _k_0;
      o[2] = _k_1;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    } else {
      o[0] = 0;
      o[1] = 1;
      o[2] = _next_3;
      o[3] = 1;
      o[4] = _k_0;
      o[5] = _k_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_103(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _s_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_0;
      o[3] = _r_5;
      o[4] = _r_6;
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

INLINE Term spin_104(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  Term _cap_1 = r0;
  Term _s_0 = r1;
  u32 _grew_0 = r2;
  WL_SPIN
    if (_grew_0 == 1) {
      o[0] = 0;
      o[1] = 0;
    } else {
      Term _o_0[2];
      if (spin_69(e, _o_0, _cap_1, _s_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_105(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
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

INLINE Term spin_106(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _r_0 = r0;
  Term _r_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_15(e, _o_0, _r_0, _r_1) == 0) {
      return 0;
    }
    o[0] = _o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_107(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _c_2 = r0;
  Term _c_3 = r1;
  WL_SPIN
    if (_c_2 == 0) {
      o[0] = 3;
      o[1] = 0;
    } else {
      o[0] = 2;
      o[1] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_108(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _x_2 = r0;
  Term _x_3 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    Term _v_1 = 0;
    Term _o_0[1];
    if (spin_15(e, _o_0, _x_3, _rest_0) == 0) {
      return 0;
    }
    _v_1 = _o_0[0];
    Term _o_1[1];
    if (spin_72(e, _o_1, _x_2, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_109(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _r_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[3];
      if (spin_73(e, _o_1, _v_0, _r_2) == 0) {
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

INLINE Term spin_110(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _k_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _k_0;
      o[3] = _r_5;
      o[4] = 0;
      o[5] = 0;
      o[6] = _r_6;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_111(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _r_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[3];
      if (spin_74(e, _o_1, _v_0, _r_2) == 0) {
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

INLINE Term spin_112(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  Term _n_1 = r1;
  WL_SPIN
    if (_x_0 == 0) {
      o[0] = 1;
      o[1] = 0;
    } else if (_x_0 == 1) {
      o[0] = 2;
      o[1] = nat_chk(e, _n_1 + 1);
    } else {
      o[0] = 3;
      o[1] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_113(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _t_6 = r0;
  Term _t_7 = r1;
  Term _l_0 = r2;
  u32 _r_4 = r3;
  Term _r_5 = r4;
  Term _r_6 = r5;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _t_6;
      o[2] = _t_7;
      o[3] = _l_0;
      o[4] = _r_5;
      o[5] = _r_6;
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

INLINE Term spin_114(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4, Term r5, Term r6, u32 r7, u32 r8, Term r9, u32 r10, u32 r11, Term r12) {
  u32 wpoll = 0;
  Term _c_4 = r0;
  Term _c_5 = r1;
  u32 _w_8 = r2;
  Term _w_9 = r3;
  Term _w_10 = r4;
  Term _w_11 = r5;
  Term _e_2 = r6;
  u32 _o_0 = r7;
  u32 _o_1 = r8;
  Term _o_2 = r9;
  u32 _r_8 = r10;
  u32 _r_9 = r11;
  Term _r_10 = r12;
  WL_SPIN
    if (_r_8 == 0) {
      u32 _v_0 = 0;
      Term _o_3[1];
      if (spin_77(e, _o_3, _r_10) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_3[0];
      Term _o_4[1];
      if (spin_79(e, _o_4, _v_0, _c_4, _c_5, _w_8, _w_9, _w_10, _w_11, _e_2, _o_0, _o_1, _o_2, _r_9) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    } else {
      Term _o_5[1];
      if (spin_51(e, _o_5, term_ctr(CID_SCon, STAT_OFF + 72)) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_115(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _k_0;
      o[3] = _r_5;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
      o[7] = _r_6;
    } else {
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

INLINE Term spin_116(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _r_1;
      o[3] = 0;
      o[4] = _r_2;
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

INLINE Term spin_117(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_3 = r0;
  u32 _r_4 = r1;
  u32 _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_3 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _r_4;
      o[3] = _r_5;
      o[4] = _r_6;
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

INLINE Term spin_118(Env e, THR Term* o, Term r0, Term r1, Term r2, u32 r3, Term r4, u32 r5) {
  u32 wpoll = 0;
  Term _t_1 = r0;
  Term _k_0 = r1;
  Term _d_0 = r2;
  u32 _e_3 = r3;
  Term _e_4 = r4;
  u32 _e_5 = r5;
  WL_SPIN
    if (_e_3 == 0) {
      Term _a_0 = (_t_1 < _k_0 ? 0 : _t_1 - _k_0);
      Term _a_1 = (_a_0 < _d_0 ? 0 : _a_0 - _d_0);
      o[0] = 0;
      o[1] = (_e_4 < _a_1 ? _e_4 : _a_1);
      o[2] = 0;
    } else if (_e_3 == 1) {
      o[0] = 1;
      o[1] = _e_4;
      o[2] = _e_5;
    } else if (_e_3 == 2) {
      o[0] = 2;
      o[1] = 0;
      o[2] = 0;
    } else {
      o[0] = 3;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_119(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, Term r4, u32 r5, u32 r6, u32 r7, u32 r8, Term r9, u32 r10) {
  u32 wpoll = 0;
  u32 _cap_2 = r0;
  Term _cap_3 = r1;
  u32 _j_6 = r2;
  Term _j_7 = r3;
  Term _j_8 = r4;
  u32 _j_9 = r5;
  u32 _j_10 = r6;
  u32 _j_11 = r7;
  u32 _e_6 = r8;
  Term _e_7 = r9;
  u32 _e_8 = r10;
  WL_SPIN
    if (_j_6 == 1) {
      o[0] = 1;
      o[1] = _j_7;
      o[2] = _j_8;
      o[3] = _j_9;
      o[4] = _j_10;
      o[5] = _j_11;
    } else {
      if (_e_6 == 0) {
        Term _o_1[6];
        if (spin_81(e, _o_1, _cap_2, _cap_3, _j_7, _j_8, _e_7) == 0) {
          return 0;
        }
        o[0] = (u32)_o_1[0];
        o[1] = _o_1[1];
        o[2] = _o_1[2];
        o[3] = (u32)_o_1[3];
        o[4] = (u32)_o_1[4];
        o[5] = (u32)_o_1[5];
      } else if (_e_6 == 1) {
        o[0] = 1;
        o[1] = _j_7;
        o[2] = _j_8;
        o[3] = 0;
        o[4] = _e_7;
        o[5] = _e_8;
      } else if (_e_6 == 2) {
        o[0] = 1;
        o[1] = _j_7;
        o[2] = _j_8;
        o[3] = 1;
        o[4] = 0;
        o[5] = 0;
      } else {
        o[0] = 0;
        o[1] = _j_7;
        o[2] = _j_8;
        o[3] = 0;
        o[4] = 0;
        o[5] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_120(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, u32 r4, u32 r5, Term r6) {
  u32 wpoll = 0;
  u32 _j_12 = r0;
  Term _j_13 = r1;
  Term _j_14 = r2;
  u32 _j_15 = r3;
  u32 _j_16 = r4;
  u32 _j_17 = r5;
  Term _rest_0 = r6;
  WL_SPIN
    if (_j_12 == 0) {
      Term _v_0 = 0;
      Term _v_1 = 0;
      Term _o_0[1];
      if (spin_15(e, _o_0, _j_14, _rest_0) == 0) {
        return 0;
      }
      _v_1 = _o_0[0];
      Term _o_1[1];
      if (spin_15(e, _o_1, _j_13, _v_1) == 0) {
        return 0;
      }
      _v_0 = _o_1[0];
      Term _o_2[1];
      if (spin_15(e, _o_2, 0, _v_0) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _v_2 = 0;
      Term _v_3 = 0;
      Term _v_4 = 0;
      Term _o_3[1];
      if (spin_29(e, _o_3, _j_15, _j_16, _j_17, _rest_0) == 0) {
        return 0;
      }
      _v_4 = _o_3[0];
      Term _o_4[1];
      if (spin_15(e, _o_4, _j_14, _v_4) == 0) {
        return 0;
      }
      _v_3 = _o_4[0];
      Term _o_5[1];
      if (spin_15(e, _o_5, _j_13, _v_3) == 0) {
        return 0;
      }
      _v_2 = _o_5[0];
      Term _o_6[1];
      if (spin_15(e, _o_6, 1ull, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_121(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _s_0 = r1;
  WL_SPIN
    if (_n_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _s_0;
    } else if (_n_0 == 1) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _s_0;
    } else {
      Term _x_0 = (_n_0 - 2);
      term_sink(e, _s_0);
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_122(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  u32 _x_1 = r1;
  u32 _x_2 = r2;
  Term _r_0 = r3;
  Term _r_1 = r4;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_83(e, _o_0, _x_0, _x_1, _x_2, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_124(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    if (_a_0 == 0) {
      o[0] = 1;
    } else {
      Term _x_0 = (_a_0 - 1);
      if (_b_0 == 0) {
        o[0] = 0;
      } else {
        Term _y_0 = (_b_0 - 1);
        r0 = _x_0;
        r1 = _y_0;
        _a_0 = r0;
        _b_0 = r1;
        WL_AGAIN(spin_124);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_123(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _l_10 = r0;
  Term _l_11 = r1;
  Term _n_0 = r2;
  WL_SPIN
    if (_l_10 == 0) {
      o[0] = 1;
    } else {
      Term _o_0[1];
      if (spin_124(e, _o_0, _n_0, _l_11) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_125(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _wi_0 = r1;
  Term _hi_0 = r2;
  Term _wb_0 = r3;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
    } else {
      if (_wi_0 == 0) {
        if (_hi_0 == 0) {
          if (_wb_0 == 0) {
            o[0] = 0;
            o[1] = 0;
          } else {
            Term _d_0 = (_wb_0 - 1);
            o[0] = 1;
            o[1] = 1;
          }
        } else {
          Term _b_1 = (_hi_0 - 1);
          o[0] = 0;
          o[1] = 0;
        }
      } else {
        Term _a_1 = (_wi_0 - 1);
        o[0] = 1;
        o[1] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_126(Env e, THR Term* o, u32 r0, Term r1, u32 r2, u32 r3, Term r4) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  Term _t_1 = r1;
  u32 _t_2 = r2;
  u32 _t_3 = r3;
  Term _r_0 = r4;
  WL_SPIN
    if (_b_0 == 1) {
      o[0] = _r_0;
    } else {
      u64 _nd_0 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_0 + 0] = rfc_seal(e, _t_1);
      e.mem[_nd_0 + 1] = rfc_seal(e, _t_2);
      e.mem[_nd_0 + 2] = rfc_seal(e, _t_3);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _r_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_127(Env e, THR Term* o, u32 r0, Term r1, u32 r2, u32 r3, u32 r4) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  Term _t_1 = r1;
  u32 _t_2 = r2;
  u32 _t_3 = r3;
  u32 _x_2 = r4;
  WL_SPIN
    if (_b_0 == 1) {
      o[0] = _t_1;
      o[1] = _t_2;
      o[2] = _x_2;
    } else {
      o[0] = _t_1;
      o[1] = _t_2;
      o[2] = _t_3;
    }
  break;
  }
  return 1;
}

INLINE Term spin_128(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  Term _x_0 = r1;
  WL_SPIN
    if (_b_0 == 0) {
      o[0] = _x_0;
    } else {
      o[0] = nat_chk(e, _x_0 + 1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_129(Env e, THR Term* o, Term r0, u32 r1, u32 r2) {
  u32 wpoll = 0;
  Term _t_1 = r0;
  u32 _t_2 = r1;
  u32 _t_3 = r2;
  WL_SPIN
    u32 _v_3 = 0;
    u32 _v_4 = 0;
    Term _o_0[2];
    if (spin_87(e, _o_0, _t_2, _t_3) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_0[0];
    _v_4 = (u32)_o_0[1];
    Term _o_1[3];
    if (spin_88(e, _o_1, _t_1, _v_3, _v_4) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
    o[1] = (u32)_o_1[1];
    o[2] = (u32)_o_1[2];
  break;
  }
  return 1;
}

INLINE Term spin_130(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  u32 _r_4 = r1;
  u32 _r_5 = r2;
  Term _r_6 = r3;
  Term _r_7 = r4;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _n_0;
      o[2] = _r_5;
      o[3] = _r_6;
      o[4] = _r_7;
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

INLINE Term spin_131(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  Term _ivs_0 = r1;
  WL_SPIN
    Term _o_1[1];
    if (spin_89(e, _o_1, _ivs_0, _n_0, 0) == 0) {
      return 0;
    }
    o[0] = (u32)_o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_132(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3, u32 r4) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  u32 _a_1 = r1;
  Term _a_2 = r2;
  Term _rest_0 = r3;
  u32 _seen_2 = r4;
  WL_SPIN
    if (_seen_2 == 1) {
      o[0] = _rest_0;
    } else {
      u64 _nd_0 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_0 + 0] = rfc_seal(e, _a_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _a_1);
      e.mem[_nd_0 + 2] = rfc_seal(e, _a_2);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_doc_seen_At, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _rest_0);
      o[0] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_133(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _c_2 = r0;
  Term _m_0 = r1;
  u32 _r_4 = r2;
  Term _r_5 = r3;
  Term _r_6 = r4;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _c_2;
      o[3] = _m_0;
      o[4] = _r_5;
      o[5] = 0;
      o[6] = 0;
      o[7] = 0;
      o[8] = _r_6;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
      o[7] = 0;
      o[8] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_134(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _s_0 = r0;
  WL_SPIN
    if (_s_0 == 0) {
      o[0] = 0;
    } else if (_s_0 == 1) {
      o[0] = 0;
    } else if (_s_0 == 2) {
      o[0] = 1;
    } else if (_s_0 == 3) {
      o[0] = 0;
    } else if (_s_0 == 4) {
      o[0] = 0;
    } else {
      o[0] = 1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_135(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _hit_0 = r0;
  Term _i_2 = r1;
  u32 _rest_0 = r2;
  Term _rest_1 = r3;
  WL_SPIN
    if (_hit_0 == 1) {
      o[0] = 1;
      o[1] = _i_2;
    } else {
      o[0] = _rest_0;
      o[1] = _rest_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_136(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _p_2 = r0;
  Term _p_3 = r1;
  WL_SPIN
    if (_p_3 == 0) {
      o[0] = 0;
    } else {
      Term _m_0 = (_p_3 - 1);
      o[0] = 1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_137(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _ok_0 = r0;
  Term _p_4 = r1;
  Term _p_5 = r2;
  WL_SPIN
    if (_ok_0 == 1) {
      Term _v_1 = 0;
      Term _v_2 = 0;
      Term _o_1[2];
      if (spin_96(e, _o_1, _p_4, _p_5) == 0) {
        return 0;
      }
      _v_1 = _o_1[0];
      _v_2 = _o_1[1];
      o[0] = 3;
      o[1] = 0;
      o[2] = _v_1;
      o[3] = _v_2;
    } else {
      o[0] = 4;
      o[1] = 0;
      o[2] = _p_4;
      o[3] = _p_5;
    }
  break;
  }
  return 1;
}

INLINE Term spin_138(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4, u32 r5, Term r6, u32 r7, Term r8, Term r9) {
  u32 wpoll = 0;
  u32 _g_10 = r0;
  Term _g_11 = r1;
  Term _g_12 = r2;
  Term _g_13 = r3;
  Term _g_14 = r4;
  u32 _look_0 = r5;
  Term _look_1 = r6;
  u32 _d_6 = r7;
  Term _d_7 = r8;
  Term _d_8 = r9;
  WL_SPIN
    if (_d_6 == 0) {
      o[0] = 0;
      o[1] = 1;
      o[2] = _g_10;
      o[3] = _g_11;
      o[4] = _g_12;
      o[5] = _g_13;
      o[6] = _g_14;
      o[7] = _look_0;
      o[8] = _look_1;
      o[9] = _d_7;
      o[10] = _d_8;
    } else {
      o[0] = 1;
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
    }
  break;
  }
  return 1;
}

INLINE Term spin_139(Env e, THR Term* o, Term r0, u32 r1, Term r2, u32 r3, u32 r4, Term r5) {
  u32 wpoll = 0;
  Term _p_1 = r0;
  u32 _sel_0 = r1;
  Term _sel_1 = r2;
  u32 _d_4 = r3;
  u32 _d_5 = r4;
  Term _d_6 = r5;
  WL_SPIN
    if (_d_4 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _p_1;
      o[3] = _sel_0;
      o[4] = _sel_1;
      o[5] = _d_5;
      o[6] = 0;
      o[7] = 0;
      o[8] = 0;
      o[9] = 0;
      o[10] = _d_6;
    } else {
      o[0] = 1;
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
    }
  break;
  }
  return 1;
}

INLINE Term spin_140(Env e, THR Term* o, Term r0, Term r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _a_1 = r1;
  Term _a_2 = r2;
  Term _b_0 = r3;
  Term _b_1 = r4;
  Term _b_2 = r5;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_0(e, _o_0, _a_0, _b_0) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    u32 _v_2 = 0;
    u32 _v_3 = 0;
    Term _o_1[1];
    if (spin_0(e, _o_1, _a_1, _b_1) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_1[0];
    u32 _v_4 = 0;
    Term _o_2[1];
    if (spin_0(e, _o_2, _a_2, _b_2) == 0) {
      return 0;
    }
    _v_4 = (u32)_o_2[0];
    Term _o_3[1];
    if (spin_34(e, _o_3, _v_3, _v_4) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_3[0];
    Term _o_4[1];
    if (spin_34(e, _o_4, _v_1, _v_2) == 0) {
      return 0;
    }
    o[0] = (u32)_o_4[0];
  break;
  }
  return 1;
}

INLINE Term spin_141(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _w_0 = r0;
  Term _need_1 = r1;
  WL_SPIN
    if (_w_0 == 0) {
      o[0] = 1;
    } else {
      Term _x_0 = (_w_0 - 1);
      Term _o_0[1];
      if (spin_2(e, _o_0, (nat_chk(e, _x_0 + 1) < _need_1)) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_142(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  Term _p_1 = r1;
  Term _s_1 = r2;
  WL_SPIN
    if (_b_0 == 1) {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
    } else {
      o[0] = 2;
      o[1] = _p_1;
      o[2] = _s_1;
      o[3] = 5ull;
    }
  break;
  }
  return 1;
}

INLINE Term spin_143(Env e, THR Term* o, u32 r0, Term r1, u32 r2, u32 r3, u32 r4, u32 r5, u32 r6, Term r7, Term r8) {
  u32 wpoll = 0;
  u32 _saved_4 = r0;
  Term _saved_5 = r1;
  u32 _cat_2 = r2;
  u32 _key_2 = r3;
  u32 _out_0 = r4;
  u32 _r_4 = r5;
  u32 _r_5 = r6;
  Term _r_6 = r7;
  Term _r_7 = r8;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _saved_4;
      o[2] = _saved_5;
      o[3] = _cat_2;
      o[4] = _key_2;
      o[5] = _out_0;
      o[6] = _r_5;
      o[7] = _r_6;
      o[8] = _r_7;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
      o[7] = 0;
      o[8] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_144(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  Term _m_1 = r0;
  u32 _out_1 = r1;
  u32 _next_2 = r2;
  Term _next_3 = r3;
  WL_SPIN
    if (_out_1 == 1) {
      Term _o_0[6];
      if (spin_102(e, _o_0, _m_1, 2, _next_2, _next_3) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
      o[2] = _o_0[2];
      o[3] = (u32)_o_0[3];
      o[4] = _o_0[4];
      o[5] = (u32)_o_0[5];
    } else {
      o[0] = 0;
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

INLINE Term spin_145(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  Term _t_1 = r0;
  Term _cap_1 = r1;
  u32 _p_3 = r2;
  Term _p_4 = r3;
  Term _p_5 = r4;
  Term _work_1 = r5;
  WL_SPIN
    if (_p_3 == 0) {
      o[0] = 0;
      o[1] = 0;
    } else {
      Term _a_0 = 1ull;
      Term _a_1 = (_t_1 < _a_0 ? 0 : _t_1 - _a_0);
      Term _o_0[2];
      if (spin_104(e, _o_0, _cap_1, (_p_4 < _a_1 ? _p_4 : _a_1), (_p_5 < _work_1)) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_146(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _g_0 = r0;
  Term _g_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    if (_g_0 == 0) {
      Term _v_2 = 0;
      Term _o_2[1];
      if (spin_15(e, _o_2, _g_1, _rest_0) == 0) {
        return 0;
      }
      _v_2 = _o_2[0];
      Term _o_3[1];
      if (spin_15(e, _o_3, 0, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    } else {
      Term _v_3 = 0;
      Term _o_4[1];
      if (spin_15(e, _o_4, _g_1, _rest_0) == 0) {
        return 0;
      }
      _v_3 = _o_4[0];
      Term _o_5[1];
      if (spin_15(e, _o_5, 1ull, _v_3) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_147(Env e, THR Term* o, u32 r0, Term r1) {
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

INLINE Term spin_148(Env e, THR Term* o) {
  u32 wpoll = 0;
  WL_SPIN
    Term _o_3[1];
    if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 164)) == 0) {
      return 0;
    }
    o[0] = _o_3[0];
  break;
  }
  return 1;
}

INLINE Term spin_149(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _a_0 = r0;
  Term _a_1 = r1;
  u32 _b_2 = r2;
  Term _b_3 = r3;
  WL_SPIN
    if (_a_0 == 0) {
      if (_b_2 == 0) {
        o[0] = 1;
      } else {
        o[0] = 0;
      }
    } else {
      if (_b_2 == 0) {
        o[0] = 0;
      } else {
        Term _o_0[1];
        if (spin_0(e, _o_0, _a_1, _b_3) == 0) {
          return 0;
        }
        o[0] = (u32)_o_0[0];
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_150(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, u32 r3, Term r4) {
  u32 wpoll = 0;
  u32 _calm_0 = r0;
  u32 _still_0 = r1;
  u32 _same_0 = r2;
  u32 _c_2 = r3;
  Term _c_3 = r4;
  WL_SPIN
    if (_calm_0 == 1) {
      o[0] = 0;
      o[1] = 0;
    } else {
      if (_still_0 == 1) {
        Term _o_4[2];
        if (spin_107(e, _o_4, _c_2, _c_3) == 0) {
          return 0;
        }
        o[0] = (u32)_o_4[0];
        o[1] = (u32)_o_4[1];
      } else {
        if (_same_0 == 1) {
          o[0] = 0;
          o[1] = 1;
        } else {
          o[0] = 1;
          o[1] = 0;
        }
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_151(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
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

INLINE Term spin_152(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  Term _x_1 = r1;
  Term _r_0 = r2;
  Term _r_1 = r3;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_108(e, _o_0, _x_0, _x_1, _r_1) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    o[0] = nat_chk(e, _r_0 + 1);
    o[1] = _v_0;
  break;
  }
  return 1;
}

INLINE Term spin_153(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  Term _r_4 = r4;
  Term _r_5 = r5;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = _r_1;
      o[3] = _r_2;
      o[4] = _r_3;
      o[5] = _r_4;
      o[6] = _r_5;
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
      o[6] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_154(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, u32 r5) {
  u32 wpoll = 0;
  u32 _ph_5 = r0;
  u32 _ph_6 = r1;
  Term _ph_7 = r2;
  Term _ph_8 = r3;
  Term _ph_9 = r4;
  u32 _del_0 = r5;
  WL_SPIN
    if (_ph_5 == 0) {
      if (_del_0 == 1) {
        o[0] = 1;
        o[1] = 2;
        o[2] = 1ull;
        o[3] = 0;
        o[4] = 0;
      } else {
        o[0] = 2;
        o[1] = 0;
        o[2] = 0;
        o[3] = 0;
        o[4] = 0;
      }
    } else if (_ph_5 == 1) {
      o[0] = 1;
      o[1] = _ph_6;
      o[2] = _ph_7;
      o[3] = 0;
      o[4] = 0;
    } else {
      o[0] = 2;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_155(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _p_0 = r0;
  u32 _p_1 = r1;
  Term _p_2 = r2;
  Term _p_3 = r3;
  Term _p_4 = r4;
  Term _rest_0 = r5;
  WL_SPIN
    if (_p_0 == 0) {
      Term _v_5 = 0;
      Term _o_1[1];
      if (spin_26(e, _o_1, _p_1, _p_2, _p_3, _p_4, _rest_0) == 0) {
        return 0;
      }
      _v_5 = _o_1[0];
      Term _o_2[1];
      if (spin_15(e, _o_2, 0, _v_5) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else if (_p_0 == 1) {
      Term _v_6 = 0;
      Term _v_7 = 0;
      Term _o_3[1];
      if (spin_15(e, _o_3, _p_2, _rest_0) == 0) {
        return 0;
      }
      _v_7 = _o_3[0];
      Term _o_4[1];
      if (spin_28(e, _o_4, _p_1, _v_7) == 0) {
        return 0;
      }
      _v_6 = _o_4[0];
      Term _o_5[1];
      if (spin_15(e, _o_5, 1ull, _v_6) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    } else {
      Term _o_6[1];
      if (spin_15(e, _o_6, 2ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_156(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_157(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _f_2 = r0;
  u32 _f_3 = r1;
  Term _n_1 = r2;
  WL_SPIN
    if (_f_2 == 0) {
      o[0] = 0;
      o[1] = _n_1;
    } else {
      Term _o_0[2];
      if (spin_112(e, _o_0, _f_3, _n_1) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_158(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _m_0 = r0;
  Term _m_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    if (_m_0 == 0) {
      Term _v_2 = 0;
      Term _o_2[1];
      if (spin_15(e, _o_2, _m_1, _rest_0) == 0) {
        return 0;
      }
      _v_2 = _o_2[0];
      Term _o_3[1];
      if (spin_15(e, _o_3, 0, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    } else if (_m_0 == 1) {
      Term _o_4[1];
      if (spin_15(e, _o_4, 1ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    } else if (_m_0 == 2) {
      Term _v_3 = 0;
      Term _o_5[1];
      if (spin_15(e, _o_5, _m_1, _rest_0) == 0) {
        return 0;
      }
      _v_3 = _o_5[0];
      Term _o_6[1];
      if (spin_15(e, _o_6, 2ull, _v_3) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    } else {
      Term _o_7[1];
      if (spin_15(e, _o_7, 3ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_7[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_159(Env e, THR Term* o, Term r0, u32 r1, Term r2, u32 r3, Term r4, Term r5, u32 r6, u32 r7, u32 r8, u32 r9, Term r10, u32 r11) {
  u32 wpoll = 0;
  Term _t_1 = r0;
  u32 _cap_2 = r1;
  Term _cap_3 = r2;
  u32 _j_6 = r3;
  Term _j_7 = r4;
  Term _j_8 = r5;
  u32 _j_9 = r6;
  u32 _j_10 = r7;
  u32 _j_11 = r8;
  u32 _e_3 = r9;
  Term _e_4 = r10;
  u32 _e_5 = r11;
  WL_SPIN
    if (_j_6 == 0) {
      u32 _v_6 = 0;
      Term _v_7 = 0;
      u32 _v_8 = 0;
      Term _o_0[3];
      if (spin_118(e, _o_0, _t_1, _j_7, _j_8, _e_3, _e_4, _e_5) == 0) {
        return 0;
      }
      _v_6 = (u32)_o_0[0];
      _v_7 = _o_0[1];
      _v_8 = (u32)_o_0[2];
      Term _o_1[6];
      if (spin_119(e, _o_1, _cap_2, _cap_3, 0, _j_7, _j_8, 0, 0, 0, _v_6, _v_7, _v_8) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = _o_1[1];
      o[2] = _o_1[2];
      o[3] = (u32)_o_1[3];
      o[4] = (u32)_o_1[4];
      o[5] = (u32)_o_1[5];
    } else {
      o[0] = 1;
      o[1] = _j_7;
      o[2] = _j_8;
      o[3] = _j_9;
      o[4] = _j_10;
      o[5] = _j_11;
    }
  break;
  }
  return 1;
}

INLINE Term spin_160(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, u32 r4, u32 r5, u32 r6, Term r7, u32 r8) {
  u32 wpoll = 0;
  u32 _j_12 = r0;
  Term _j_13 = r1;
  Term _j_14 = r2;
  u32 _j_15 = r3;
  u32 _j_16 = r4;
  u32 _j_17 = r5;
  u32 _e_6 = r6;
  Term _e_7 = r7;
  u32 _e_8 = r8;
  WL_SPIN
    if (_j_12 == 1) {
      o[0] = term_pak(CID_Nil, 0);
    } else {
      if (_e_6 == 0) {
        o[0] = term_pak(CID_Nil, 0);
      } else if (_e_6 == 1) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _e_7);
        e.mem[_nd_0 + 1] = rfc_seal(e, _e_8);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_job_Exited, _nd_0));
        e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
        o[0] = term_ctr(CID_Con, _nd_1);
      } else if (_e_6 == 2) {
        o[0] = term_ctr(CID_Con, STAT_OFF + 104);
      } else {
        o[0] = term_pak(CID_Nil, 0);
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_161(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _l_0 = r0;
  Term _l_1 = r1;
  u32 _r_6 = r2;
  Term _r_7 = r3;
  Term _r_8 = r4;
  WL_SPIN
    if (_r_6 == 0) {
      o[0] = 0;
      o[1] = 4;
      o[2] = _l_0;
      o[3] = _l_1;
      o[4] = _r_7;
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

INLINE Term spin_162(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      Term _o_0[3];
      if (spin_121(e, _o_0, _r_1, _r_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = (u32)_o_0[1];
      o[2] = _o_0[2];
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_163(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, u32 r3) {
  u32 wpoll = 0;
  u32 _b_0 = r0;
  u32 _s_0 = r1;
  u32 _r_0 = r2;
  u32 _r_1 = r3;
  WL_SPIN
    if (_b_0 == 1) {
      o[0] = 1;
      o[1] = _s_0;
    } else {
      o[0] = _r_0;
      o[1] = _r_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_164(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _n_0 = r0;
  WL_SPIN
    if (_n_0 == 0) {
      o[0] = 1;
    } else {
      Term _p_0 = (_n_0 - 1);
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_165(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _free_0 = r0;
  WL_SPIN
    if (_free_0 == 1) {
      o[0] = 2;
    } else {
      o[0] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_166(Env e, THR Term* o, u32 r0, Term r1, u32 r2) {
  u32 wpoll = 0;
  u32 _s_0 = r0;
  Term _k_5 = r1;
  u32 _c_0 = r2;
  WL_SPIN
    if (_s_0 == 0) {
      u64 _nd_0 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_0 + 0] = rfc_seal(e, _k_5);
      e.mem[_nd_0 + 1] = rfc_seal(e, _c_0);
      e.mem[_nd_0 + 2] = rfc_seal(e, 0);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
      o[0] = term_ctr(CID_Con, _nd_1);
    } else if (_s_0 == 1) {
      u64 _nd_2 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_2 + 0] = rfc_seal(e, _k_5);
      e.mem[_nd_2 + 1] = rfc_seal(e, _c_0);
      e.mem[_nd_2 + 2] = rfc_seal(e, 1);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_2));
      e.mem[_nd_3 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
      o[0] = term_ctr(CID_Con, _nd_3);
    } else if (_s_0 == 2) {
      u64 _nd_4 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_4 + 0] = rfc_seal(e, _k_5);
      e.mem[_nd_4 + 1] = rfc_seal(e, _c_0);
      e.mem[_nd_4 + 2] = rfc_seal(e, 2);
      u64 _nd_5 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_5 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_4));
      e.mem[_nd_5 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
      o[0] = term_ctr(CID_Con, _nd_5);
    } else if (_s_0 == 3) {
      u64 _nd_6 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_6 + 0] = rfc_seal(e, _k_5);
      e.mem[_nd_6 + 1] = rfc_seal(e, _c_0);
      e.mem[_nd_6 + 2] = rfc_seal(e, 3);
      u64 _nd_7 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_7 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_6));
      e.mem[_nd_7 + 1] = rfc_seal(e, term_pak(CID_Nil, 0));
      o[0] = term_ctr(CID_Con, _nd_7);
    } else {
      o[0] = term_pak(CID_Nil, 0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_167(Env e, THR Term* o, u32 r0, u32 r1) {
  u32 wpoll = 0;
  u32 _free_0 = r0;
  u32 _full_0 = r1;
  WL_SPIN
    if (_free_0 == 1) {
      o[0] = 2;
    } else {
      if (_full_0 == 1) {
        o[0] = 4;
      } else {
        o[0] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_168(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _lo_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _lo_0;
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

INLINE Term spin_169(Env e, THR Term* o, Term r0, u32 r1, Term r2, u32 r3, Term r4, Term r5) {
  u32 wpoll = 0;
  Term _x_0 = r0;
  u32 _x_1 = r1;
  Term _x_2 = r2;
  u32 _r_0 = r3;
  Term _r_1 = r4;
  Term _r_2 = r5;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      e.mem[_nd_2 + 2] = rfc_seal(e, _x_2);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_doc_seen_At, _nd_2));
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

INLINE Term spin_170(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _le_0 = r0;
  Term _c_0 = r1;
  Term _cap_1 = r2;
  WL_SPIN
    if (_le_0 == 1) {
      o[0] = _c_0;
    } else {
      o[0] = _cap_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_171(Env e, THR Term* o, u32 r0) {
  u32 wpoll = 0;
  u32 _s_0 = r0;
  WL_SPIN
    if (_s_0 == 0) {
      o[0] = 1;
      o[1] = 0;
    } else if (_s_0 == 1) {
      o[0] = 1;
      o[1] = 0;
    } else if (_s_0 == 2) {
      o[0] = 0;
      o[1] = 0;
    } else if (_s_0 == 3) {
      o[0] = 0;
      o[1] = 0;
    } else if (_s_0 == 4) {
      o[0] = 0;
      o[1] = 0;
    } else {
      o[0] = 0;
      o[1] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_172(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _hit_0 = r0;
  Term _hit_1 = r1;
  Term _p_4 = r2;
  Term _p_5 = r3;
  WL_SPIN
    if (_hit_0 == 1) {
      o[0] = 2;
      o[1] = _hit_1;
      o[2] = _p_4;
      o[3] = _p_5;
    } else {
      u32 _v_2 = 0;
      Term _o_1[1];
      if (spin_136(e, _o_1, _p_4, _p_5) == 0) {
        return 0;
      }
      _v_2 = (u32)_o_1[0];
      Term _o_2[4];
      if (spin_137(e, _o_2, _v_2, _p_4, _p_5) == 0) {
        return 0;
      }
      o[0] = (u32)_o_2[0];
      o[1] = _o_2[1];
      o[2] = _o_2[2];
      o[3] = _o_2[3];
    }
  break;
  }
  return 1;
}

INLINE Term spin_173(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  Term _p_1 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    Term _v_1 = 0;
    Term _o_0[1];
    if (spin_15(e, _o_0, _p_1, _rest_1) == 0) {
      return 0;
    }
    _v_1 = _o_0[0];
    Term _o_1[1];
    if (spin_15(e, _o_1, _p_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_174(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _a_0 = r0;
  Term _a_1 = r1;
  Term _rest_2 = r2;
  WL_SPIN
    if (_a_0 == 0) {
      Term _o_3[1];
      if (spin_15(e, _o_3, 0, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    } else if (_a_0 == 1) {
      Term _o_4[1];
      if (spin_15(e, _o_4, 1ull, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    } else if (_a_0 == 2) {
      Term _v_2 = 0;
      Term _o_5[1];
      if (spin_15(e, _o_5, _a_1, _rest_2) == 0) {
        return 0;
      }
      _v_2 = _o_5[0];
      Term _o_6[1];
      if (spin_15(e, _o_6, 2ull, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    } else if (_a_0 == 3) {
      Term _o_7[1];
      if (spin_15(e, _o_7, 3ull, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_7[0];
    } else {
      Term _o_8[1];
      if (spin_15(e, _o_8, 4ull, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_8[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_175(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, u32 r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  u32 _d_10 = r4;
  Term _d_11 = r5;
  Term _d_12 = r6;
  WL_SPIN
    if (_d_10 == 0) {
      o[0] = 0;
      o[1] = 2;
      o[2] = _r_0;
      o[3] = _r_1;
      o[4] = _r_2;
      o[5] = _r_3;
      o[6] = _d_11;
      o[7] = 0;
      o[8] = 0;
      o[9] = 0;
      o[10] = _d_12;
    } else {
      o[0] = 1;
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
    }
  break;
  }
  return 1;
}

INLINE Term spin_176(Env e, THR Term* o, Term r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  u32 _d_4 = r1;
  u32 _d_5 = r2;
  Term _d_6 = r3;
  Term _d_7 = r4;
  WL_SPIN
    if (_d_4 == 0) {
      u32 _v_0 = 0;
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _o_0[3];
      if (spin_43(e, _o_0, _d_7) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      _v_1 = (u32)_o_0[1];
      _v_2 = _o_0[2];
      Term _o_1[11];
      if (spin_139(e, _o_1, _p_0, _d_5, _d_6, _v_0, _v_1, _v_2) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = (u32)_o_1[1];
      o[2] = _o_1[2];
      o[3] = _o_1[3];
      o[4] = _o_1[4];
      o[5] = _o_1[5];
      o[6] = _o_1[6];
      o[7] = (u32)_o_1[7];
      o[8] = _o_1[8];
      o[9] = _o_1[9];
      o[10] = _o_1[10];
    } else {
      o[0] = 1;
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
    }
  break;
  }
  return 1;
}

INLINE Term spin_177(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _seen_0 = r0;
  Term _k_0 = r1;
  Term _k_1 = r2;
  Term _k_2 = r3;
  Term _sh_2 = r4;
  WL_SPIN
    if (_seen_0 == 1) {
      o[0] = _sh_2;
    } else {
      u64 _nd_0 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_0 + 0] = rfc_seal(e, _k_0);
      e.mem[_nd_0 + 1] = rfc_seal(e, _k_1);
      e.mem[_nd_0 + 2] = rfc_seal(e, _k_2);
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_aux_fallback_K, _nd_0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _sh_2);
      o[0] = term_ctr(CID_Con, _nd_1);
    }
  break;
  }
  return 1;
}

INLINE Term spin_178(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _seen_0 = r0;
  Term _k_0 = r1;
  Term _k_1 = r2;
  Term _k_2 = r3;
  Term _t_4 = r4;
  WL_SPIN
    if (_seen_0 == 1) {
      o[0] = _t_4;
    } else {
      u64 _nd_3 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_3 + 0] = rfc_seal(e, _k_0);
      e.mem[_nd_3 + 1] = rfc_seal(e, _k_1);
      e.mem[_nd_3 + 2] = rfc_seal(e, _k_2);
      u64 _nd_4 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_4 + 0] = rfc_seal(e, term_ctr(CID_aux_fallback_Note, _nd_3));
      e.mem[_nd_4 + 1] = rfc_seal(e, _t_4);
      o[0] = term_ctr(CID_Con, _nd_4);
    }
  break;
  }
  return 1;
}

INLINE Term spin_179(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  Term _s_0 = r1;
  u32 _look_2 = r2;
  Term _look_3 = r3;
  Term _need_1 = r4;
  WL_SPIN
    if (_look_2 == 0) {
      o[0] = 2;
      o[1] = _p_0;
      o[2] = _s_0;
      o[3] = _look_3;
    } else {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_141(e, _o_0, _look_3, _need_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[4];
      if (spin_142(e, _o_1, _v_0, _p_0, _s_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = _o_1[1];
      o[2] = _o_1[2];
      o[3] = _o_1[3];
    }
  break;
  }
  return 1;
}

INLINE Term spin_180(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  Term _r_3 = r3;
  Term _rest_1 = r4;
  WL_SPIN
    if (_r_0 == 0) {
      Term _o_0[1];
      if (spin_15(e, _o_0, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else if (_r_0 == 1) {
      Term _o_1[1];
      if (spin_15(e, _o_1, 1ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _v_1 = 0;
      Term _o_2[1];
      if (spin_39(e, _o_2, _r_1, _r_2, _r_3, _rest_1) == 0) {
        return 0;
      }
      _v_1 = _o_2[0];
      Term _o_3[1];
      if (spin_15(e, _o_3, 2ull, _v_1) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_181(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_182(Env e, THR Term* o, Term r0, u32 r1, u32 r2, u32 r3, Term r4) {
  u32 wpoll = 0;
  Term _m_1 = r0;
  u32 _key_1 = r1;
  u32 _out_1 = r2;
  u32 _next_2 = r3;
  Term _next_3 = r4;
  WL_SPIN
    if (_key_1 == 1) {
      Term _o_0[6];
      if (spin_144(e, _o_0, _m_1, _out_1, _next_2, _next_3) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
      o[2] = _o_0[2];
      o[3] = (u32)_o_0[3];
      o[4] = _o_0[4];
      o[5] = (u32)_o_0[5];
    } else {
      o[0] = 2;
      o[1] = _m_1;
      o[2] = 1;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_183(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _rest_1 = r1;
  WL_SPIN
    if (_r_0 == 0) {
      Term _o_0[1];
      if (spin_15(e, _o_0, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else if (_r_0 == 1) {
      Term _o_1[1];
      if (spin_15(e, _o_1, 1ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_15(e, _o_2, 2ull, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_184(Env e, THR Term* o, Term r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  Term _k_0 = r0;
  u32 _k_1 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    Term _v_1 = 0;
    Term _o_1[1];
    if (spin_183(e, _o_1, _k_1, _rest_1) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    Term _o_2[1];
    if (spin_15(e, _o_2, _k_0, _v_1) == 0) {
      return 0;
    }
    o[0] = _o_2[0];
  break;
  }
  return 1;
}

INLINE Term spin_185(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _left_0 = r0;
  Term _t_1 = r1;
  Term _cap_1 = r2;
  u32 _p_3 = r3;
  Term _p_4 = r4;
  Term _p_5 = r5;
  Term _work_0 = r6;
  WL_SPIN
    if (_left_0 == 1) {
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _o_1[2];
      if (spin_145(e, _o_1, _t_1, _cap_1, _p_3, _p_4, _p_5, _work_0) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      _v_2 = _o_1[1];
      Term _o_2[1];
      if (spin_146(e, _o_2, _v_1, _v_2, term_pak(CID_SNil, 0)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _o_3[1];
      if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 120)) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_186(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, u32 r4, Term r5) {
  u32 wpoll = 0;
  u32 _p_2 = r0;
  Term _p_3 = r1;
  u32 _b_2 = r2;
  Term _b_3 = r3;
  u32 _c_2 = r4;
  Term _c_3 = r5;
  WL_SPIN
    u32 _v_2 = 0;
    Term _o_0[1];
    if (spin_149(e, _o_0, _c_2, _c_3, _b_2, _b_3) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_0[0];
    u32 _v_3 = 0;
    Term _o_1[1];
    if (spin_149(e, _o_1, _p_2, _p_3, _b_2, _b_3) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_1[0];
    u32 _v_4 = 0;
    Term _o_2[1];
    if (spin_149(e, _o_2, _p_2, _p_3, _c_2, _c_3) == 0) {
      return 0;
    }
    _v_4 = (u32)_o_2[0];
    Term _o_3[2];
    if (spin_150(e, _o_3, _v_2, _v_3, _v_4, _c_2, _c_3) == 0) {
      return 0;
    }
    o[0] = (u32)_o_3[0];
    o[1] = (u32)_o_3[1];
  break;
  }
  return 1;
}

INLINE Term spin_187(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  u32 _x_1 = r1;
  Term _rest_0 = r2;
  WL_SPIN
    if (_x_0 == 0) {
      Term _v_5 = 0;
      Term _o_5[1];
      if (spin_147(e, _o_5, _x_1, _rest_0) == 0) {
        return 0;
      }
      _v_5 = _o_5[0];
      Term _o_6[1];
      if (spin_15(e, _o_6, 0, _v_5) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    } else if (_x_0 == 1) {
      Term _o_7[1];
      if (spin_15(e, _o_7, 1ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_7[0];
    } else if (_x_0 == 2) {
      Term _o_8[1];
      if (spin_15(e, _o_8, 2ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_8[0];
    } else {
      Term _o_9[1];
      if (spin_15(e, _o_9, 3ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_9[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_188(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _o_0 = r0;
  u32 _o_1 = r1;
  u32 _r_6 = r2;
  Term _r_7 = r3;
  Term _r_8 = r4;
  WL_SPIN
    if (_r_6 == 0) {
      o[0] = 0;
      o[1] = _o_0;
      o[2] = _o_1;
      o[3] = _r_7;
      o[4] = _r_8;
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

INLINE Term spin_189(Env e, THR Term* o, u32 r0, u32 r1, u32 r2) {
  u32 wpoll = 0;
  u32 _en_0 = r0;
  u32 _en_1 = r1;
  u32 _c_1 = r2;
  WL_SPIN
    if (_en_0 == 0) {
      o[0] = _c_1;
    } else {
      o[0] = _en_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_190(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3, Term r4, Term r5, u32 r6) {
  u32 wpoll = 0;
  u32 _left_0 = r0;
  u32 _ph_5 = r1;
  u32 _ph_6 = r2;
  Term _ph_7 = r3;
  Term _ph_8 = r4;
  Term _ph_9 = r5;
  u32 _d_0 = r6;
  WL_SPIN
    if (_left_0 == 1) {
      u32 _v_1 = 0;
      u32 _v_2 = 0;
      Term _v_3 = 0;
      Term _v_4 = 0;
      Term _v_5 = 0;
      Term _o_1[5];
      if (spin_154(e, _o_1, _ph_5, _ph_6, _ph_7, _ph_8, _ph_9, _d_0) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      _v_2 = (u32)_o_1[1];
      _v_3 = _o_1[2];
      _v_4 = _o_1[3];
      _v_5 = _o_1[4];
      Term _o_2[1];
      if (spin_155(e, _o_2, _v_1, _v_2, _v_3, _v_4, _v_5, term_pak(CID_SNil, 0)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _o_3[1];
      if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 42)) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_191(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _left_0 = r0;
  u32 _f_2 = r1;
  u32 _f_3 = r2;
  Term _n_0 = r3;
  WL_SPIN
    if (_left_0 == 1) {
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _o_1[2];
      if (spin_157(e, _o_1, _f_2, _f_3, _n_0) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      _v_2 = _o_1[1];
      Term _o_2[1];
      if (spin_158(e, _o_2, _v_1, _v_2, term_pak(CID_SNil, 0)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _o_3[1];
      if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 42)) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_192(Env e, THR Term* o, Term r0, u32 r1, Term r2, Term r3) {
  u32 wpoll = 0;
  Term _st_0 = r0;
  u32 _r_4 = r1;
  Term _r_5 = r2;
  Term _r_6 = r3;
  WL_SPIN
    if (_r_4 == 0) {
      o[0] = 0;
      o[1] = _st_0;
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

INLINE Term spin_193(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3) {
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

INLINE Term spin_194(Env e, THR Term* o, u32 r0) {
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

INLINE Term spin_195(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_196(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_197(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 0;
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

INLINE Term spin_198(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
  u32 wpoll = 0;
  u32 _r_3 = r0;
  Term _r_4 = r1;
  Term _r_5 = r2;
  Term _t_4 = r3;
  WL_SPIN
    if (_r_3 == 0) {
      if (_t_4 == 0) {
        o[0] = 0;
        o[1] = 1;
        o[2] = _r_4;
        o[3] = 0;
        o[4] = 0;
        o[5] = _r_5;
      } else if (_t_4 == 1) {
        o[0] = 0;
        o[1] = 2;
        o[2] = _r_4;
        o[3] = 0;
        o[4] = 0;
        o[5] = _r_5;
      } else {
        Term _b_0 = (_t_4 - 2);
        o[0] = 0;
        o[1] = 3;
        o[2] = _r_4;
        o[3] = 0;
        o[4] = 0;
        o[5] = _r_5;
      }
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

INLINE Term spin_199(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _l_0 = r0;
  Term _l_1 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    if (_l_0 == 0) {
      Term _o_2[1];
      if (spin_15(e, _o_2, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _v_2 = 0;
      Term _o_3[1];
      if (spin_15(e, _o_3, _l_1, _rest_1) == 0) {
        return 0;
      }
      _v_2 = _o_3[0];
      Term _o_4[1];
      if (spin_15(e, _o_4, 1ull, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_200(Env e, THR Term* o, Term r0, Term r1) {
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

INLINE Term spin_201(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4) {
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
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_doc_seen_Iv, _nd_2));
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

INLINE Term spin_202(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _d_0 = r0;
  Term _d_1 = r1;
  Term _d_2 = r2;
  Term _d_3 = r3;
  Term _rest_0 = r4;
  WL_SPIN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_173(e, _o_0, _d_2, _d_3, _rest_0) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    Term _o_1[1];
    if (spin_174(e, _o_1, _d_0, _d_1, _v_0) == 0) {
      return 0;
    }
    o[0] = _o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_203(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _l_0 = r0;
  Term _l_1 = r1;
  Term _cap_0 = r2;
  WL_SPIN
    if (_cap_0 == 0) {
      o[0] = _l_0;
      o[1] = _l_1;
    } else {
      Term _x_0 = (_cap_0 - 1);
      Term _v_3 = 0;
      u32 _v_4 = 0;
      Term _o_3[1];
      if (spin_32(e, _o_3, _l_0, nat_chk(e, _x_0 + 1)) == 0) {
        return 0;
      }
      _v_4 = (u32)_o_3[0];
      Term _o_4[1];
      if (spin_170(e, _o_4, _v_4, _l_0, nat_chk(e, _x_0 + 1)) == 0) {
        return 0;
      }
      _v_3 = _o_4[0];
      o[0] = _v_3;
      o[1] = _l_1;
    }
  break;
  }
  return 1;
}

INLINE Term spin_204(Env e, THR Term* o, Term r0, Term r1, Term r2) {
  u32 wpoll = 0;
  Term _l_2 = r0;
  Term _l_3 = r1;
  Term _rest_1 = r2;
  WL_SPIN
    Term _v_5 = 0;
    Term _o_6[1];
    if (spin_15(e, _o_6, _l_3, _rest_1) == 0) {
      return 0;
    }
    _v_5 = _o_6[0];
    Term _o_7[1];
    if (spin_15(e, _o_7, _l_2, _v_5) == 0) {
      return 0;
    }
    o[0] = _o_7[0];
  break;
  }
  return 1;
}

INLINE Term spin_205(Env e, THR Term* o, Term r0, u32 r1, Term r2, u32 r3) {
  u32 wpoll = 0;
  Term _p_0 = r0;
  u32 _sel_0 = r1;
  Term _sel_1 = r2;
  u32 _ok_0 = r3;
  WL_SPIN
    if (_sel_0 == 0) {
      o[0] = 0;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else if (_sel_0 == 1) {
      o[0] = 0;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
    } else {
      if (_ok_0 == 1) {
        o[0] = 1;
        o[1] = _p_0;
        o[2] = _sel_1;
        o[3] = 0;
        o[4] = 0;
      } else {
        o[0] = 0;
        o[1] = 2;
        o[2] = _p_0;
        o[3] = _sel_1;
        o[4] = 0;
      }
    }
  break;
  }
  return 1;
}

INLINE Term spin_206(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _g_0 = r0;
  Term _g_1 = r1;
  Term _g_2 = r2;
  Term _g_3 = r3;
  Term _g_4 = r4;
  Term _rest_0 = r5;
  WL_SPIN
    if (_g_0 == 0) {
      Term _v_5 = 0;
      Term _o_1[1];
      if (spin_180(e, _o_1, _g_1, _g_2, _g_3, _g_4, _rest_0) == 0) {
        return 0;
      }
      _v_5 = _o_1[0];
      Term _o_2[1];
      if (spin_15(e, _o_2, 0, _v_5) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _v_6 = 0;
      Term _v_7 = 0;
      Term _o_3[1];
      if (spin_15(e, _o_3, _g_2, _rest_0) == 0) {
        return 0;
      }
      _v_7 = _o_3[0];
      Term _o_4[1];
      if (spin_15(e, _o_4, _g_1, _v_7) == 0) {
        return 0;
      }
      _v_6 = _o_4[0];
      Term _o_5[1];
      if (spin_15(e, _o_5, 1ull, _v_6) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_207(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3, Term r4, u32 r5, Term r6, Term r7) {
  u32 wpoll = 0;
  u32 _g_5 = r0;
  Term _g_6 = r1;
  Term _g_7 = r2;
  Term _g_8 = r3;
  Term _g_9 = r4;
  u32 _look_0 = r5;
  Term _look_1 = r6;
  Term _need_0 = r7;
  WL_SPIN
    if (_g_5 == 0) {
      o[0] = _g_6;
      o[1] = _g_7;
      o[2] = _g_8;
      o[3] = _g_9;
    } else {
      Term _o_7[4];
      if (spin_179(e, _o_7, _g_6, _g_7, _look_0, _look_1, _need_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_7[0];
      o[1] = _o_7[1];
      o[2] = _o_7[2];
      o[3] = _o_7[3];
    }
  break;
  }
  return 1;
}

INLINE Term spin_208(Env e, THR Term* o, u32 r0, Term r1) {
  u32 wpoll = 0;
  u32 _next_0 = r0;
  Term _next_1 = r1;
  WL_SPIN
    if (_next_0 == 0) {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    } else {
      o[0] = 0;
      o[1] = 1;
      o[2] = _next_1;
      o[3] = 0;
      o[4] = 0;
      o[5] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_209(Env e, THR Term* o, Term r0, u32 r1, u32 r2, u32 r3, u32 r4, Term r5) {
  u32 wpoll = 0;
  Term _m_0 = r0;
  u32 _cat_0 = r1;
  u32 _key_0 = r2;
  u32 _out_0 = r3;
  u32 _next_2 = r4;
  Term _next_3 = r5;
  WL_SPIN
    if (_cat_0 == 1) {
      Term _o_1[6];
      if (spin_182(e, _o_1, _m_0, _key_0, _out_0, _next_2, _next_3) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = _o_1[1];
      o[2] = _o_1[2];
      o[3] = (u32)_o_1[3];
      o[4] = _o_1[4];
      o[5] = (u32)_o_1[5];
    } else {
      Term _o_2[6];
      if (spin_102(e, _o_2, _m_0, 0, _next_2, _next_3) == 0) {
        return 0;
      }
      o[0] = (u32)_o_2[0];
      o[1] = _o_2[1];
      o[2] = _o_2[2];
      o[3] = (u32)_o_2[3];
      o[4] = _o_2[4];
      o[5] = (u32)_o_2[5];
    }
  break;
  }
  return 1;
}

INLINE Term spin_210(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3) {
  u32 wpoll = 0;
  u32 _s_0 = r0;
  Term _s_1 = r1;
  u32 _s_2 = r2;
  Term _rest_1 = r3;
  WL_SPIN
    if (_s_0 == 0) {
      Term _o_0[1];
      if (spin_15(e, _o_0, 0, _rest_1) == 0) {
        return 0;
      }
      o[0] = _o_0[0];
    } else {
      Term _v_2 = 0;
      Term _o_1[1];
      if (spin_184(e, _o_1, _s_1, _s_2, _rest_1) == 0) {
        return 0;
      }
      _v_2 = _o_1[0];
      Term _o_2[1];
      if (spin_15(e, _o_2, 1ull, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_211(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _p_0 = r0;
  Term _p_1 = r1;
  Term _rest_2 = r2;
  WL_SPIN
    if (_p_0 == 0) {
      Term _o_4[1];
      if (spin_15(e, _o_4, 0, _rest_2) == 0) {
        return 0;
      }
      o[0] = _o_4[0];
    } else {
      Term _v_3 = 0;
      Term _o_5[1];
      if (spin_15(e, _o_5, _p_1, _rest_2) == 0) {
        return 0;
      }
      _v_3 = _o_5[0];
      Term _o_6[1];
      if (spin_15(e, _o_6, 1ull, _v_3) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_212(Env e, THR Term* o, Term r0, Term r1, u32 r2, Term r3, Term r4, u32 r5, Term r6, Term r7) {
  u32 wpoll = 0;
  Term _t_4 = r0;
  Term _cap_2 = r1;
  u32 _p_0 = r2;
  Term _p_1 = r3;
  Term _p_2 = r4;
  u32 _r_8 = r5;
  Term _r_9 = r6;
  Term _r_10 = r7;
  WL_SPIN
    if (_r_8 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_77(e, _o_0, _r_10) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[1];
      if (spin_185(e, _o_1, _v_0, _t_4, _cap_2, _p_0, _p_1, _p_2, _r_9) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_51(e, _o_2, term_ctr(CID_SCon, STAT_OFF + 248)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_213(Env e, THR Term* o, u32 r0, u32 r1, Term r2) {
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

INLINE Term spin_214(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      o[0] = 0;
      o[1] = 1;
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

INLINE Term spin_215(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, Term r4, u32 r5, Term r6) {
  u32 wpoll = 0;
  u32 _left_0 = r0;
  u32 _p_2 = r1;
  Term _p_3 = r2;
  u32 _b_2 = r3;
  Term _b_3 = r4;
  u32 _c_0 = r5;
  Term _c_1 = r6;
  WL_SPIN
    if (_left_0 == 1) {
      u32 _v_1 = 0;
      u32 _v_2 = 0;
      Term _o_1[2];
      if (spin_186(e, _o_1, _p_2, _p_3, _b_2, _b_3, _c_0, _c_1) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      _v_2 = (u32)_o_1[1];
      Term _o_2[1];
      if (spin_187(e, _o_2, _v_1, _v_2, term_pak(CID_SNil, 0)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _o_3[1];
      if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 262)) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_216(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, Term r4, Term r5) {
  u32 wpoll = 0;
  u32 _x_0 = r0;
  u32 _x_1 = r1;
  Term _x_2 = r2;
  u32 _r_0 = r3;
  Term _r_1 = r4;
  Term _r_2 = r5;
  WL_SPIN
    if (_r_0 == 0) {
      u64 _nd_2 = heap_alloc(e, cls_fit(3));
      e.mem[_nd_2 + 0] = rfc_seal(e, _x_0);
      e.mem[_nd_2 + 1] = rfc_seal(e, _x_1);
      e.mem[_nd_2 + 2] = rfc_seal(e, _x_2);
      u64 _nd_3 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_3 + 0] = rfc_seal(e, term_ctr(CID_doc_lines_Run, _nd_2));
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

INLINE Term spin_217(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, u32 r5, u32 r6, Term r7) {
  u32 wpoll = 0;
  u32 _ph_0 = r0;
  u32 _ph_1 = r1;
  Term _ph_2 = r2;
  Term _ph_3 = r3;
  Term _ph_4 = r4;
  u32 _r_7 = r5;
  u32 _r_8 = r6;
  Term _r_9 = r7;
  WL_SPIN
    if (_r_7 == 0) {
      u32 _v_3 = 0;
      Term _o_1[1];
      if (spin_77(e, _o_1, _r_9) == 0) {
        return 0;
      }
      _v_3 = (u32)_o_1[0];
      Term _o_2[1];
      if (spin_190(e, _o_2, _v_3, _ph_0, _ph_1, _ph_2, _ph_3, _ph_4, _r_8) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _o_3[1];
      if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 306)) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_218(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _f_0 = r0;
  u32 _f_1 = r1;
  u32 _r_6 = r2;
  Term _r_7 = r3;
  Term _r_8 = r4;
  WL_SPIN
    if (_r_6 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_77(e, _o_0, _r_8) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[1];
      if (spin_191(e, _o_1, _v_0, _f_0, _f_1, _r_7) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_51(e, _o_2, term_ctr(CID_SCon, STAT_OFF + 332)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_219(Env e, THR Term* o, u32 r0, Term r1, u32 r2) {
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
      if (spin_194(e, _o_0, _comma_0) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
    }
  break;
  }
  return 1;
}

INLINE Term spin_220(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _l_2 = r0;
  Term _l_3 = r1;
  Term _q_1 = r2;
  WL_SPIN
    o[0] = _l_2;
    o[1] = _l_3;
    o[2] = _q_1;
    o[3] = term_pak(CID_Nil, 0);
    o[4] = 0;
  break;
  }
  return 1;
}

INLINE Term spin_221(Env e, THR Term* o, u32 r0, Term r1, u32 r2, u32 r3, u32 r4, u32 r5, Term r6) {
  u32 wpoll = 0;
  u32 _x_7 = r0;
  Term _x_8 = r1;
  u32 _x_9 = r2;
  u32 _x_10 = r3;
  u32 _x_11 = r4;
  u32 _x_12 = r5;
  Term _x_13 = r6;
  WL_SPIN
    if (_x_7 == 0) {
      Term _o_0[6];
      if (spin_208(e, _o_0, _x_12, _x_13) == 0) {
        return 0;
      }
      o[0] = (u32)_o_0[0];
      o[1] = _o_0[1];
      o[2] = _o_0[2];
      o[3] = (u32)_o_0[3];
      o[4] = _o_0[4];
      o[5] = (u32)_o_0[5];
    } else {
      Term _o_1[6];
      if (spin_209(e, _o_1, _x_8, _x_9, _x_10, _x_11, _x_12, _x_13) == 0) {
        return 0;
      }
      o[0] = (u32)_o_1[0];
      o[1] = _o_1[1];
      o[2] = _o_1[2];
      o[3] = (u32)_o_1[3];
      o[4] = _o_1[4];
      o[5] = (u32)_o_1[5];
    }
  break;
  }
  return 1;
}

INLINE Term spin_222(Env e, THR Term* o, u32 r0, Term r1, Term r2, u32 r3, Term r4, u32 r5, Term r6) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  u32 _r_3 = r3;
  Term _r_4 = r4;
  u32 _r_5 = r5;
  Term _rest_0 = r6;
  WL_SPIN
    if (_r_0 == 0) {
      Term _v_6 = 0;
      Term _v_7 = 0;
      Term _o_3[1];
      if (spin_210(e, _o_3, _r_3, _r_4, _r_5, _rest_0) == 0) {
        return 0;
      }
      _v_7 = _o_3[0];
      Term _o_4[1];
      if (spin_211(e, _o_4, _r_1, _r_2, _v_7) == 0) {
        return 0;
      }
      _v_6 = _o_4[0];
      Term _o_5[1];
      if (spin_15(e, _o_5, 0, _v_6) == 0) {
        return 0;
      }
      o[0] = _o_5[0];
    } else if (_r_0 == 1) {
      Term _o_6[1];
      if (spin_15(e, _o_6, 1ull, _rest_0) == 0) {
        return 0;
      }
      o[0] = _o_6[0];
    } else {
      Term _v_8 = 0;
      Term _o_7[1];
      if (spin_184(e, _o_7, _r_1, _r_2, _rest_0) == 0) {
        return 0;
      }
      _v_8 = _o_7[0];
      Term _o_8[1];
      if (spin_15(e, _o_8, 2ull, _v_8) == 0) {
        return 0;
      }
      o[0] = _o_8[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_223(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _x_0 = ((u64)(u32)(_r_1));
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_0(e, _o_0, ((u64)_x_0), _r_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[3];
      if (spin_213(e, _o_1, _v_0, _x_0, _r_2) == 0) {
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

INLINE Term spin_224(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, u32 r4, u32 r5, Term r6, Term r7) {
  u32 wpoll = 0;
  u32 _p_4 = r0;
  Term _p_5 = r1;
  u32 _b_0 = r2;
  Term _b_1 = r3;
  u32 _r_6 = r4;
  u32 _r_7 = r5;
  Term _r_8 = r6;
  Term _r_9 = r7;
  WL_SPIN
    if (_r_6 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_77(e, _o_0, _r_9) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[1];
      if (spin_215(e, _o_1, _v_0, _p_4, _p_5, _b_0, _b_1, _r_7, _r_8) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_51(e, _o_2, term_ctr(CID_SCon, STAT_OFF + 516)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_225(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  Term _r_1 = r1;
  Term _r_2 = r2;
  WL_SPIN
    if (_r_0 == 0) {
      if (_r_1 == 0) {
        o[0] = 0;
        o[1] = 0;
        o[2] = _r_2;
      } else if (_r_1 == 1) {
        o[0] = 0;
        o[1] = 1;
        o[2] = _r_2;
      } else {
        Term _p_0 = (_r_1 - 2);
        term_sink(e, _r_2);
        o[0] = 1;
        o[1] = 0;
        o[2] = 0;
      }
    } else {
      o[0] = 1;
      o[1] = 0;
      o[2] = 0;
    }
  break;
  }
  return 1;
}

INLINE Term spin_226(Env e, THR Term* o, u32 r0, u32 r1, u32 r2, Term r3, Term r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  u32 _r_2 = r2;
  Term _r_3 = r3;
  Term _r_4 = r4;
  Term _r_5 = r5;
  Term _r_6 = r6;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _v_0 = 0;
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _o_7[3];
      if (spin_43(e, _o_7, _r_6) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_7[0];
      _v_1 = (u32)_o_7[1];
      _v_2 = _o_7[2];
      Term _o_8[1];
      if (spin_217(e, _o_8, _r_1, _r_2, _r_3, _r_4, _r_5, _v_0, _v_1, _v_2) == 0) {
        return 0;
      }
      o[0] = _o_8[0];
    } else {
      Term _o_9[1];
      if (spin_51(e, _o_9, term_ctr(CID_SCon, STAT_OFF + 562)) == 0) {
        return 0;
      }
      o[0] = _o_9[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_227(Env e, THR Term* o, u32 r0, Term r1, u32 r2, Term r3, Term r4) {
  u32 wpoll = 0;
  u32 _l_0 = r0;
  Term _l_1 = r1;
  u32 _r_6 = r2;
  Term _r_7 = r3;
  Term _r_8 = r4;
  WL_SPIN
    if (_r_6 == 0) {
      o[0] = 0;
      o[1] = _l_0;
      o[2] = _l_1;
      o[3] = _r_7;
      o[4] = _r_8;
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

INLINE Term spin_228(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, u32 r4, u32 r5, u32 r6, Term r7) {
  u32 wpoll = 0;
  u32 _done_0 = r0;
  u32 _x_0 = r1;
  Term _x_1 = r2;
  u32 _x_2 = r3;
  u32 _x_3 = r4;
  u32 _x_4 = r5;
  u32 _x_5 = r6;
  Term _x_6 = r7;
  WL_SPIN
    if (_done_0 == 1) {
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _v_3 = 0;
      u32 _v_4 = 0;
      Term _v_5 = 0;
      u32 _v_6 = 0;
      Term _o_1[6];
      if (spin_221(e, _o_1, _x_0, _x_1, _x_2, _x_3, _x_4, _x_5, _x_6) == 0) {
        return 0;
      }
      _v_1 = (u32)_o_1[0];
      _v_2 = _o_1[1];
      _v_3 = _o_1[2];
      _v_4 = (u32)_o_1[3];
      _v_5 = _o_1[4];
      _v_6 = (u32)_o_1[5];
      Term _o_2[1];
      if (spin_222(e, _o_2, _v_1, _v_2, _v_3, _v_4, _v_5, _v_6, term_pak(CID_SNil, 0)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    } else {
      Term _o_3[1];
      if (spin_51(e, _o_3, term_ctr(CID_SCon, STAT_OFF + 792)) == 0) {
        return 0;
      }
      o[0] = _o_3[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_229(Env e, THR Term* o, u32 r0, u32 r1, Term r2, u32 r3, u32 r4, u32 r5, u32 r6, Term r7, Term r8) {
  u32 wpoll = 0;
  u32 _r_0 = r0;
  u32 _r_1 = r1;
  Term _r_2 = r2;
  u32 _r_3 = r3;
  u32 _r_4 = r4;
  u32 _r_5 = r5;
  u32 _r_6 = r6;
  Term _r_7 = r7;
  Term _r_8 = r8;
  WL_SPIN
    if (_r_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_77(e, _o_0, _r_8) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      Term _o_1[1];
      if (spin_228(e, _o_1, _v_0, _r_1, _r_2, _r_3, _r_4, _r_5, _r_6, _r_7) == 0) {
        return 0;
      }
      o[0] = _o_1[0];
    } else {
      Term _o_2[1];
      if (spin_51(e, _o_2, term_ctr(CID_SCon, STAT_OFF + 1138)) == 0) {
        return 0;
      }
      o[0] = _o_2[0];
    }
  break;
  }
  return 1;
}

INLINE Term spin_230(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
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
    o[4] = 0;
    o[5] = 0;
    o[6] = 0;
    o[7] = _r_3;
  break;
  }
  return 1;
}

INLINE Term spin_231(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _r_4 = r0;
  u32 _r_5 = r1;
  Term _r_6 = r2;
  Term _r_7 = r3;
  Term _r_8 = r4;
  Term _r_9 = r5;
  Term _r_10 = r6;
  WL_SPIN
    o[0] = 1;
    o[1] = _r_4;
    o[2] = _r_5;
    o[3] = _r_6;
    o[4] = _r_7;
    o[5] = _r_8;
    o[6] = _r_9;
    o[7] = _r_10;
  break;
  }
  return 1;
}

INLINE Term spin_232(Env e, THR Term* o, Term r0) {
  u32 wpoll = 0;
  Term _input_1 = r0;
  WL_SPIN
    o[0] = _input_1;
  break;
  }
  return 1;
}

INLINE Term spin_233(Env e, THR Term* o, u32 r0, Term r1, Term r2, Term r3) {
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
    o[4] = 0;
    o[5] = 0;
    o[6] = 0;
    o[7] = _r_3;
  break;
  }
  return 1;
}

INLINE Term spin_234(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _r_4 = r0;
  u32 _r_5 = r1;
  Term _r_6 = r2;
  Term _r_7 = r3;
  Term _r_8 = r4;
  Term _r_9 = r5;
  Term _r_10 = r6;
  WL_SPIN
    o[0] = 1;
    o[1] = _r_4;
    o[2] = _r_5;
    o[3] = _r_6;
    o[4] = _r_7;
    o[5] = _r_8;
    o[6] = _r_9;
    o[7] = _r_10;
  break;
  }
  return 1;
}

INLINE Term spin_235(Env e, THR Term* o, u32 r0, u32 r1, Term r2, Term r3, Term r4, Term r5, Term r6) {
  u32 wpoll = 0;
  u32 _state_7 = r0;
  u32 _state_8 = r1;
  Term _state_9 = r2;
  Term _state_10 = r3;
  Term _state_11 = r4;
  Term _state_12 = r5;
  Term _state_13 = r6;
  WL_SPIN
    if (_state_7 == 0) {
      term_sink(e, _state_10);
      o[0] = term_pak(CID_Unit, 0);
    } else if (_state_7 == 1) {
      term_sink(e, _state_12);
      o[0] = term_pak(CID_Unit, 0);
    } else {
      o[0] = term_pak(CID_Unit, 0);
    }
  break;
  }
  return 1;
}

INLINE Term spin_236(Env e, THR Term* o, Term r0, Term r1, u32 r2) {
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
          WL_AGAIN(spin_236);
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

INLINE Term spin_237(Env e, THR Term* o, Term r0) {
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

INLINE Term spin_238(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_1 = r0;
  Term _b_1 = r1;
  WL_SPIN
    Term _o_0[1];
    if (spin_236(e, _o_0, _a_1, _b_1, 1) == 0) {
      return 0;
    }
    o[0] = (u32)_o_0[0];
  break;
  }
  return 1;
}

INLINE Term spin_239(Env e, THR Term* o, Term r0, Term r1) {
  u32 wpoll = 0;
  Term _a_0 = r0;
  Term _b_0 = r1;
  WL_SPIN
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_238(e, _o_0, _a_0, _b_0) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_1(e, _o_1, _v_1) == 0) {
      return 0;
    }
    o[0] = (u32)_o_1[0];
  break;
  }
  return 1;
}

INLINE Term spin_240(Env e, THR Term* o, u32 r0, Term r1, Term r2) {
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
  WL_CASE(FID_ffi_workflow_get_row)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_workflow_get_row_k50;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_workflow_get_row_k50, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_workflow_get_row_k50, _t_0);
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
  WL_CASE(FID_ffi_workflow_get_row_k50)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_workflow_get_row_k51;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_workflow_get_row_k51, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_workflow_get_row_k51, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_sts)) {
        u64 _t_3 = task_node(e, FID_ffi_workflow_get_sts, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_workflow_get_sts, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_workflow_get_sts);
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
  WL_CASE(FID_ffi_workflow_get_row_k51)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_22(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = (u32)_o_0[2];
    r3 = _o_0[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_7)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    u32 _cur_2 = r3;
    Term _cur_3 = r4;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_workflow_Row, _nd_0));
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
          STK(3) = FID_wire_get_list_go_7_k53;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_7_k53, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          WL_CONT = term_tsk(FID_wire_get_list_go_7_k53, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_row)) {
          u64 _t_1 = task_node(e, FID_ffi_workflow_get_row, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_3;
          return term_tsk(FID_ffi_workflow_get_row, _t_1);
        }
        r0 = _cur_3;
        WL_JMP(FID_ffi_workflow_get_row);
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
  WL_CASE(FID_wire_get_list_go_7_k53)
    WL_POPN(3);
    Term _m_1 = STK(0);
    Term _cur_4 = STK(1);
    u32 _cur_5 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    u32 _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _cur_4;
      STK(1) = _cur_5;
      STK(2) = FID_wire_get_list_go_7_k54;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_7_k54, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_4;
      e.mem[_t_2 + 1] = _cur_5;
      WL_CONT = term_tsk(FID_wire_get_list_go_7_k54, _t_2);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_7)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_7, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      return term_tsk(FID_wire_get_list_go_7, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    WL_JMP(FID_wire_get_list_go_7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_7_k54)
    WL_POPN(2);
    Term _cur_6 = STK(0);
    u32 _cur_7 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_37(e, _o_0, _cur_6, _cur_7, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_job_get_end)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_job_get_end_k77;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_job_get_end_k77, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_job_get_end_k77, _t_0);
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
  WL_CASE(FID_ffi_job_get_end_k77)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_job_get_end_k78;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_job_get_end_k78, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_job_get_end_k78, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_job_get_code)) {
          u64 _t_3 = task_node(e, FID_ffi_job_get_code, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_job_get_code, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_job_get_code);
      } else if (_h_1 == 1) {
        r0 = 0;
        r1 = 1;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else {
        Term _q_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_job_get_end_k78)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    u32 _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_14(e, _o_0, _h_3, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = (u32)_o_0[2];
    r3 = (u32)_o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_9)
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
      u32 _o_1 = 0;
      u32 _o_2 = 0;
      if (term_aux(_f_0) == CID_job_Exited) {
        _o_0 = 0;
        Term _fb_1[2];
        u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
        u32 _f_2 = _fb_1[0];
        u32 _f_3 = _fb_1[1];
        spare_free(e, cls_fit(2), _sp_1);
        _o_1 = _f_2;
        _o_2 = _f_3;
      } else {
        _o_0 = 1;
      }
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _o_0;
        STK(1) = _o_1;
        STK(2) = _o_2;
        STK(3) = FID_wire_put_list_go_9_k84;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_9_k84, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _o_0;
        e.mem[_t_0 + 1] = _o_1;
        e.mem[_t_0 + 2] = _o_2;
        WL_CONT = term_tsk(FID_wire_put_list_go_9_k84, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_9);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_9_k84)
    WL_POPN(3);
    u32 _o_3 = STK(0);
    u32 _o_4 = STK(1);
    u32 _o_5 = STK(2);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_7[2];
    if (spin_54(e, _o_7, _o_3, _o_4, _o_5, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_7[0];
    r1 = _o_7[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_fits)
    Term _us_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_us_0) == CID_Nil) {
      r0 = 1;
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _us_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_3;
        STK(1) = _f_4;
        STK(2) = FID_doc_seen_fits_k95;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_doc_seen_fits_k95, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_3;
        e.mem[_t_0 + 1] = _f_4;
        WL_CONT = term_tsk(FID_doc_seen_fits_k95, _t_0);
        WL_IDX = 2;
      }
      r0 = _f_1;
      _us_0 = r0;
      WL_AGAIN(FID_doc_seen_fits);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_fits_k95)
    WL_POPN(2);
    u32 _f_5 = STK(0);
    Term _f_6 = STK(1);
    u32 _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_1[1];
    if (spin_61(e, _o_1, _f_5, _f_6) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    Term _o_2[1];
    if (spin_34(e, _o_2, _v_0, _h_0) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_sts)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_workflow_get_sts_k100;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_workflow_get_sts_k100, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_workflow_get_sts_k100, _t_0);
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
  WL_CASE(FID_ffi_workflow_get_sts_k100)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_1[3];
    if (spin_64(e, _o_1, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_pool)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_workflow_get_pool_k105;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_workflow_get_pool_k105, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_workflow_get_pool_k105, _t_0);
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
  WL_CASE(FID_ffi_workflow_get_pool_k105)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_workflow_get_pool_k106;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_workflow_get_pool_k106, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_workflow_get_pool_k106, _t_2);
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
  WL_CASE(FID_ffi_workflow_get_pool_k106)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_38(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_ffi_aux_fallback_get_key)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_aux_fallback_get_key_k111;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_aux_fallback_get_key_k111, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_aux_fallback_get_key_k111, _t_0);
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
  WL_CASE(FID_ffi_aux_fallback_get_key_k111)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_aux_fallback_get_key_k112;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_aux_fallback_get_key_k112, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_key_k112, _t_2);
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
      r4 = 0;
      WL_RETN(5);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_key_k112)
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
        STK(2) = FID_ffi_aux_fallback_get_key_k113;
        WL_PUSHN(3);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_aux_fallback_get_key_k113, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_6;
        e.mem[_t_4 + 1] = _h_4;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_key_k113, _t_4);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_wire_get_nat, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_aux_fallback_get_key_k113)
    WL_POPN(2);
    Term _h_10 = STK(0);
    Term _h_11 = STK(1);
    u32 _h_7 = r0;
    Term _h_8 = r1;
    Term _h_9 = r2;
    WL_OPEN
    Term _o_0[5];
    if (spin_23(e, _o_0, _h_10, _h_11, _h_7, _h_8, _h_9) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_1)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    Term _cur_2 = r3;
    Term _cur_3 = r4;
    Term _cur_4 = r5;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(3));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        e.mem[_nd_0 + 2] = rfc_seal(e, _cur_3);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_aux_fallback_K, _nd_0));
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
          STK(4) = FID_wire_get_list_go_1_k115;
          WL_PUSHN(5);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_1_k115, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          e.mem[_t_0 + 3] = _cur_3;
          WL_CONT = term_tsk(FID_wire_get_list_go_1_k115, _t_0);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_key)) {
          u64 _t_1 = task_node(e, FID_ffi_aux_fallback_get_key, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_4;
          return term_tsk(FID_ffi_aux_fallback_get_key, _t_1);
        }
        r0 = _cur_4;
        WL_JMP(FID_ffi_aux_fallback_get_key);
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
  WL_CASE(FID_wire_get_list_go_1_k115)
    WL_POPN(4);
    Term _m_1 = STK(0);
    Term _cur_5 = STK(1);
    Term _cur_6 = STK(2);
    Term _cur_7 = STK(3);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _cur_5;
      STK(1) = _cur_6;
      STK(2) = _cur_7;
      STK(3) = FID_wire_get_list_go_1_k116;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_1_k116, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_5;
      e.mem[_t_2 + 1] = _cur_6;
      e.mem[_t_2 + 2] = _cur_7;
      WL_CONT = term_tsk(FID_wire_get_list_go_1_k116, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_1)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      e.mem[_t_3 + 5] = _h_4;
      return term_tsk(FID_wire_get_list_go_1, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    r5 = _h_4;
    WL_JMP(FID_wire_get_list_go_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_1_k116)
    WL_POPN(3);
    Term _cur_8 = STK(0);
    Term _cur_9 = STK(1);
    Term _cur_10 = STK(2);
    u32 _h_5 = r0;
    Term _h_6 = r1;
    Term _h_7 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_65(e, _o_0, _cur_8, _cur_9, _cur_10, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_6)
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
          STK(2) = FID_wire_get_list_go_6_k132;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_6_k132, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          WL_CONT = term_tsk(FID_wire_get_list_go_6_k132, _t_0);
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
  WL_CASE(FID_wire_get_list_go_6_k132)
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
      STK(1) = FID_wire_get_list_go_6_k133;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_6_k133, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_3;
      WL_CONT = term_tsk(FID_wire_get_list_go_6_k133, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_6)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_6, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      return term_tsk(FID_wire_get_list_go_6, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    WL_JMP(FID_wire_get_list_go_6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_6_k133)
    WL_POPN(1);
    Term _cur_4 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_70(e, _o_0, _cur_4, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
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
        STK(1) = FID_wire_put_str_go_k135;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_str_go_k135, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_put_str_go_k135, _t_0);
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
  WL_CASE(FID_wire_put_str_go_k135)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_71(e, _o_0, _f_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    r1 = _o_0[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_mode)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_mode_k151;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_mode_k151, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_mode_k151, _t_0);
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
  WL_CASE(FID_ffi_child_get_mode_k151)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_2[3];
    if (spin_76(e, _o_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_job_get_code)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_job_get_code_k157;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_job_get_code_k157, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_job_get_code_k157, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_u32)) {
      u64 _t_1 = task_node(e, FID_wire_get_u32, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_wire_get_u32, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_wire_get_u32);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_job_get_code_k157)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_job_get_code_k158;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_job_get_code_k158, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_job_get_code_k158, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_u32)) {
        u64 _t_3 = task_node(e, FID_wire_get_u32, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_wire_get_u32, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_wire_get_u32);
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
  WL_CASE(FID_ffi_job_get_code_k158)
    WL_POPN(1);
    u32 _h_6 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_52(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_wire_put_list_9)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_9_k164;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_9_k164, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_9_k164, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_9)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_9, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _xs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_9, _t_1);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_9);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_9_k164)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[1];
    if (spin_82(e, _o_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_mark)
    u32 _c_0 = r0;
    Term _ts_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ts_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ts_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      u32 _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      _f_1 = term_keep(e, _f_1, 1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _c_0;
        STK(1) = _f_2;
        STK(2) = _f_3;
        STK(3) = _f_4;
        STK(4) = _f_1;
        STK(5) = FID_admission_lv_mark_k170;
        WL_PUSHN(6);
      } else {
        u64 _t_0 = task_node(e, FID_admission_lv_mark_k170, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _c_0;
        e.mem[_t_0 + 1] = _f_2;
        e.mem[_t_0 + 2] = _f_3;
        e.mem[_t_0 + 3] = _f_4;
        e.mem[_t_0 + 4] = _f_1;
        WL_CONT = term_tsk(FID_admission_lv_mark_k170, _t_0);
        WL_IDX = 5;
      }
      r0 = _c_0;
      r1 = _f_1;
      _c_0 = r0;
      _ts_0 = r1;
      WL_AGAIN(FID_admission_lv_mark);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_mark_k170)
    WL_POPN(5);
    u32 _c_1 = STK(0);
    Term _f_5 = STK(1);
    u32 _f_6 = STK(2);
    u32 _f_7 = STK(3);
    Term _f_8 = STK(4);
    Term _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_4[1];
    if (spin_84(e, _o_4, 1, _c_1, _f_5, _f_6, _f_7) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_4[0];
    Term _o_5[1];
    if (spin_86(e, _o_5, _v_0, _c_1, _f_5, _f_6, _f_7, _f_8, _h_0) == 0) {
      return 0;
    }
    r0 = _o_5[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_doc_seen_get_mnat)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_doc_seen_get_mnat_k177;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_doc_seen_get_mnat_k177, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_doc_seen_get_mnat_k177, _t_0);
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
  WL_CASE(FID_ffi_doc_seen_get_mnat_k177)
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
          STK(0) = FID_ffi_doc_seen_get_mnat_k178;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_doc_seen_get_mnat_k178, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_doc_seen_get_mnat_k178, _t_2);
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
        Term _p_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_doc_seen_get_mnat_k178)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_59(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
        STK(0) = FID_List_length_k184;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_List_length_k184, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_List_length_k184, _t_0);
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
  WL_CASE(FID_List_length_k184)
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _h_0 + 1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_whole_go)
    u32 _few_0 = r0;
    Term _us_0 = r1;
    WL_OPEN
    if (_few_0 == 1) {
      if (!DEVICE && !seq && fid_nofk(FID_doc_seen_fits)) {
        u64 _t_0 = task_node(e, FID_doc_seen_fits, WL_CONT, WL_IDX, 0);
        e.mem[_t_0 + 0] = _us_0;
        return term_tsk(FID_doc_seen_fits, _t_0);
      }
      r0 = _us_0;
      WL_JMP(FID_doc_seen_fits);
    } else {
      term_sink(e, _us_0);
      r0 = 0;
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_List_take)
    Term _xs_0 = r0;
    Term _n_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_xs_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _xs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      if (_n_0 == 0) {
        term_sink(e, _f_0);
        term_sink(e, _f_1);
        spare_free(e, cls_fit(2), _sp_0);
        r0 = term_pak(CID_Nil, 0);
        WL_RETN(1);
      } else {
        Term _p_0 = (_n_0 - 1);
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(2, 0);
          STK(0) = _f_0;
          STK(1) = FID_List_take_k188;
          WL_PUSHN(2);
        } else {
          u64 _t_0 = task_node(e, FID_List_take_k188, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_0;
          WL_CONT = term_tsk(FID_List_take_k188, _t_0);
          WL_IDX = 1;
        }
        r0 = _f_1;
        r1 = _p_0;
        _xs_0 = r0;
        _n_0 = r1;
        WL_AGAIN(FID_List_take);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_List_take_k188)
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
  WL_CASE(FID_doc_seen_shows)
    Term _us_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_us_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _us_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = FID_doc_seen_shows_k190;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_doc_seen_shows_k190, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        WL_CONT = term_tsk(FID_doc_seen_shows_k190, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      _us_0 = r0;
      WL_AGAIN(FID_doc_seen_shows);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_shows_k190)
    WL_POPN(3);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    Term _f_7 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    Term _o_2[1];
    if (spin_90(e, _o_2, _f_5, _f_6, _f_7, _h_0) == 0) {
      return 0;
    }
    r0 = _o_2[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_lines)
    Term _ats_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ats_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _ats_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      u32 _f_3 = e.mem[_sp_1 + 1];
      Term _f_4 = e.mem[_sp_1 + 2];
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = FID_doc_seen_lines_k192;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_doc_seen_lines_k192, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        WL_CONT = term_tsk(FID_doc_seen_lines_k192, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      _ats_0 = r0;
      WL_AGAIN(FID_doc_seen_lines);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_lines_k192)
    WL_POPN(3);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    Term _f_7 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_91(e, _o_0, _f_5, _f_6, _f_7) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_6)
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
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = FID_wire_put_list_go_6_k194;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_6_k194, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        WL_CONT = term_tsk(FID_wire_put_list_go_6_k194, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_6);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_6_k194)
    WL_POPN(3);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    Term _f_7 = STK(2);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_92(e, _o_1, _f_5, _f_6, _f_7, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
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
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _f_0;
        STK(1) = FID_wire_put_list_go_5_k196;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_5_k196, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_put_list_go_5_k196, _t_0);
        WL_IDX = 1;
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
  WL_CASE(FID_wire_put_list_go_5_k196)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_93(e, _o_1, _f_2, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_7)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_7_k201;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_7_k201, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_7_k201, _t_0);
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
  WL_CASE(FID_wire_get_list_7_k201)
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
          STK(1) = FID_wire_get_list_7_k202;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_7_k202, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_7_k202, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_row)) {
          u64 _t_3 = task_node(e, FID_ffi_workflow_get_row, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_workflow_get_row, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_workflow_get_row);
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
  WL_CASE(FID_wire_get_list_7_k202)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    u32 _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_7)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_7, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      return term_tsk(FID_wire_get_list_go_7, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    WL_JMP(FID_wire_get_list_go_7);
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
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = FID_wire_put_list_go_1_k227;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_1_k227, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        WL_CONT = term_tsk(FID_wire_put_list_go_1_k227, _t_0);
        WL_IDX = 3;
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
  WL_CASE(FID_wire_put_list_go_1_k227)
    WL_POPN(3);
    Term _f_5 = STK(0);
    Term _f_6 = STK(1);
    Term _f_7 = STK(2);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_100(e, _o_1, _f_5, _f_6, _f_7, _h_0, _h_1) == 0) {
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
      Term _o_2 = 0;
      Term _o_3 = 0;
      if (term_aux(_f_0) == CID_aux_fallback_Stay) {
        _o_0 = 0;
      } else if (term_aux(_f_0) == CID_aux_fallback_Went) {
        _o_0 = 1;
      } else if (term_aux(_f_0) == CID_aux_fallback_Sub) {
        _o_0 = 2;
        Term _fb_1[3];
        u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
        Term _f_2 = _fb_1[0];
        Term _f_3 = _fb_1[1];
        Term _f_4 = _fb_1[2];
        spare_free(e, cls_fit(3), _sp_1);
        _o_1 = _f_2;
        _o_2 = _f_3;
        _o_3 = _f_4;
      } else {
        _o_0 = 3;
        Term _fb_2[3];
        u64 _sp_2 = ctr_take(e, _f_0, 3, _fb_2);
        Term _f_5 = _fb_2[0];
        Term _f_6 = _fb_2[1];
        Term _f_7 = _fb_2[2];
        spare_free(e, cls_fit(3), _sp_2);
        _o_1 = _f_5;
        _o_2 = _f_6;
        _o_3 = _f_7;
      }
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _o_0;
        STK(1) = _o_1;
        STK(2) = _o_2;
        STK(3) = _o_3;
        STK(4) = FID_wire_put_list_go_2_k229;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_2_k229, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _o_0;
        e.mem[_t_0 + 1] = _o_1;
        e.mem[_t_0 + 2] = _o_2;
        e.mem[_t_0 + 3] = _o_3;
        WL_CONT = term_tsk(FID_wire_put_list_go_2_k229, _t_0);
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
  WL_CASE(FID_wire_put_list_go_2_k229)
    WL_POPN(4);
    u32 _o_4 = STK(0);
    Term _o_5 = STK(1);
    Term _o_6 = STK(2);
    Term _o_7 = STK(3);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_9[2];
    if (spin_101(e, _o_9, _o_4, _o_5, _o_6, _o_7, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_9[0];
    r1 = _o_9[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_default_model_get_next)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_default_model_get_next_k233;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_default_model_get_next_k233, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_default_model_get_next_k233, _t_0);
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
  WL_CASE(FID_ffi_default_model_get_next_k233)
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
          STK(0) = FID_ffi_default_model_get_next_k234;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_default_model_get_next_k234, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_default_model_get_next_k234, _t_2);
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
        Term _b_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_default_model_get_next_k234)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_40(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
          STK(1) = FID_wire_take_k244;
          WL_PUSHN(2);
        } else {
          u64 _t_0 = task_node(e, FID_wire_take_k244, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_0;
          WL_CONT = term_tsk(FID_wire_take_k244, _t_0);
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
  WL_CASE(FID_wire_take_k244)
    WL_POPN(1);
    u32 _f_2 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_105(e, _o_0, _f_2, _h_0, _h_1, _h_2) == 0) {
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
      STK(0) = FID_wire_put_str_k248;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_str_k248, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_str_k248, _t_0);
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
  WL_CASE(FID_wire_put_str_k248)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[1];
    if (spin_106(e, _o_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_report)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_report_k255;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_report_k255, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_report_k255, _t_0);
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
  WL_CASE(FID_ffi_child_get_report_k255)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_2[3];
    if (spin_109(e, _o_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_fate)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_fate_k262;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_fate_k262, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_fate_k262, _t_0);
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
  WL_CASE(FID_ffi_child_get_fate_k262)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_2[3];
    if (spin_111(e, _o_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_obs)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_obs_k271;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_obs_k271, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_obs_k271, _t_0);
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
  WL_CASE(FID_ffi_child_get_obs_k271)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _h_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      if (_v_0 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_child_get_obs_k272;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_child_get_obs_k272, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_child_get_obs_k272, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_maybe_nat)) {
          u64 _t_3 = task_node(e, FID_ffi_child_get_maybe_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_child_get_maybe_nat, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_child_get_maybe_nat);
      } else if (_v_0 == 1) {
        r0 = 0;
        r1 = 1;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_v_0 == 2) {
        u32 _v_1 = 0;
        u32 _v_2 = 0;
        Term _v_3 = 0;
        Term _o_2[3];
        if (spin_43(e, _o_2, _h_2) == 0) {
          return 0;
        }
        _v_1 = (u32)_o_2[0];
        _v_2 = (u32)_o_2[1];
        _v_3 = _o_2[2];
        Term _o_3[5];
        if (spin_46(e, _o_3, _v_1, _v_2, _v_3) == 0) {
          return 0;
        }
        r0 = (u32)_o_3[0];
        r1 = (u32)_o_3[1];
        r2 = (u32)_o_3[2];
        r3 = _o_3[3];
        r4 = _o_3[4];
        WL_RETN(5);
      } else if (_v_0 == 3) {
        r0 = 0;
        r1 = 3;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_v_0 == 4) {
        r0 = 0;
        r1 = 4;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else {
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
  WL_CASE(FID_ffi_child_get_obs_k272)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    Term _o_1[5];
    if (spin_42(e, _o_1, _h_3, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = (u32)_o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    WL_RETN(5);
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
      u64 _sp_0 = term_peek(e.mem, _xs_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      u32 _f_3 = e.mem[_sp_1 + 1];
      u32 _f_4 = e.mem[_sp_1 + 2];
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = FID_wire_put_list_go_0_k290;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_0_k290, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        WL_CONT = term_tsk(FID_wire_put_list_go_0_k290, _t_0);
        WL_IDX = 3;
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
  WL_CASE(FID_wire_put_list_go_0_k290)
    WL_POPN(3);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    u32 _f_7 = STK(2);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_122(e, _o_1, _f_5, _f_6, _f_7, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_pick)
    u32 _l_0 = r0;
    Term _l_1 = r1;
    Term _ts_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _l_0;
      STK(1) = _l_1;
      STK(2) = _ts_0;
      STK(3) = FID_admission_lv_pick_k292;
      WL_PUSHN(4);
    } else {
      u64 _t_0 = task_node(e, FID_admission_lv_pick_k292, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _l_0;
      e.mem[_t_0 + 1] = _l_1;
      e.mem[_t_0 + 2] = _ts_0;
      WL_CONT = term_tsk(FID_admission_lv_pick_k292, _t_0);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_held)) {
      u64 _t_1 = task_node(e, FID_admission_lv_held, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _ts_0;
      return term_tsk(FID_admission_lv_held, _t_1);
    }
    r0 = _ts_0;
    WL_JMP(FID_admission_lv_held);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_pick_k292)
    WL_POPN(3);
    u32 _l_2 = STK(0);
    Term _l_3 = STK(1);
    Term _ts_1 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _l_2;
      STK(1) = _l_3;
      STK(2) = _ts_1;
      STK(3) = _h_0;
      STK(4) = FID_admission_lv_pick_k293;
      WL_PUSHN(5);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_pick_k293, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _l_2;
      e.mem[_t_2 + 1] = _l_3;
      e.mem[_t_2 + 2] = _ts_1;
      e.mem[_t_2 + 3] = _h_0;
      WL_CONT = term_tsk(FID_admission_lv_pick_k293, _t_2);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_3 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = 1;
      e.mem[_t_3 + 1] = 0;
      e.mem[_t_3 + 2] = _ts_1;
      return term_tsk(FID_admission_lv_cnt, _t_3);
    }
    r0 = 1;
    r1 = 0;
    r2 = _ts_1;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_pick_k293)
    WL_POPN(4);
    u32 _l_4 = STK(0);
    Term _l_5 = STK(1);
    Term _ts_2 = STK(2);
    Term _h_2 = STK(3);
    Term _h_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _l_4;
      STK(1) = _l_5;
      STK(2) = _ts_2;
      STK(3) = _h_2;
      STK(4) = _h_1;
      STK(5) = FID_admission_lv_pick_k294;
      WL_PUSHN(6);
    } else {
      u64 _t_4 = task_node(e, FID_admission_lv_pick_k294, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _l_4;
      e.mem[_t_4 + 1] = _l_5;
      e.mem[_t_4 + 2] = _ts_2;
      e.mem[_t_4 + 3] = _h_2;
      e.mem[_t_4 + 4] = _h_1;
      WL_CONT = term_tsk(FID_admission_lv_pick_k294, _t_4);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_5 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = 0;
      e.mem[_t_5 + 1] = 0;
      e.mem[_t_5 + 2] = _ts_2;
      return term_tsk(FID_admission_lv_cnt, _t_5);
    }
    r0 = 0;
    r1 = 0;
    r2 = _ts_2;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_pick_k294)
    WL_POPN(5);
    u32 _l_6 = STK(0);
    Term _l_7 = STK(1);
    Term _ts_3 = STK(2);
    Term _h_4 = STK(3);
    Term _h_5 = STK(4);
    Term _h_3 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _l_6;
      STK(1) = _l_7;
      STK(2) = _h_4;
      STK(3) = _h_5;
      STK(4) = _h_3;
      STK(5) = FID_admission_lv_pick_k295;
      WL_PUSHN(6);
    } else {
      u64 _t_6 = task_node(e, FID_admission_lv_pick_k295, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _l_6;
      e.mem[_t_6 + 1] = _l_7;
      e.mem[_t_6 + 2] = _h_4;
      e.mem[_t_6 + 3] = _h_5;
      e.mem[_t_6 + 4] = _h_3;
      WL_CONT = term_tsk(FID_admission_lv_pick_k295, _t_6);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_7 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = 1;
      e.mem[_t_7 + 1] = 1;
      e.mem[_t_7 + 2] = _ts_3;
      return term_tsk(FID_admission_lv_cnt, _t_7);
    }
    r0 = 1;
    r1 = 1;
    r2 = _ts_3;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_pick_k295)
    WL_POPN(5);
    u32 _l_8 = STK(0);
    Term _l_9 = STK(1);
    Term _h_7 = STK(2);
    Term _h_8 = STK(3);
    Term _h_9 = STK(4);
    Term _h_6 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_1[1];
    if (spin_123(e, _o_1, _l_8, _l_9, _h_7) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_1[0];
    Term _o_2[2];
    if (spin_125(e, _o_2, _v_0, _h_8, _h_9, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_waits)
    Term _ts_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _ts_0;
      STK(1) = FID_admission_lv_waits_k297;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_admission_lv_waits_k297, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _ts_0;
      WL_CONT = term_tsk(FID_admission_lv_waits_k297, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_1 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = 1;
      e.mem[_t_1 + 1] = 0;
      e.mem[_t_1 + 2] = _ts_0;
      return term_tsk(FID_admission_lv_cnt, _t_1);
    }
    r0 = 1;
    r1 = 0;
    r2 = _ts_0;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_waits_k297)
    WL_POPN(1);
    Term _ts_1 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_admission_lv_waits_k298;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_waits_k298, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_admission_lv_waits_k298, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_3 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = 1;
      e.mem[_t_3 + 1] = 1;
      e.mem[_t_3 + 2] = _ts_1;
      return term_tsk(FID_admission_lv_cnt, _t_3);
    }
    r0 = 1;
    r1 = 1;
    r2 = _ts_1;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_waits_k298)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    r0 = nat_chk(e, _h_2 + _h_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_grant_go)
    Term _n_0 = r0;
    u32 _d_0 = r1;
    u32 _d_1 = r2;
    u32 _l_0 = r3;
    Term _l_1 = r4;
    Term _ts_0 = r5;
    WL_OPEN
    if (_n_0 == 0) {
      r0 = _ts_0;
      WL_RETN(1);
    } else {
      Term _f_0 = (_n_0 - 1);
      if (_d_0 == 0) {
        r0 = _ts_0;
        WL_RETN(1);
      } else {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _f_0;
          STK(1) = _l_0;
          STK(2) = _l_1;
          STK(3) = FID_admission_lv_grant_go_k300;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_admission_lv_grant_go_k300, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _f_0;
          e.mem[_t_0 + 1] = _l_0;
          e.mem[_t_0 + 2] = _l_1;
          WL_CONT = term_tsk(FID_admission_lv_grant_go_k300, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_mark)) {
          u64 _t_1 = task_node(e, FID_admission_lv_mark, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _d_1;
          e.mem[_t_1 + 1] = _ts_0;
          return term_tsk(FID_admission_lv_mark, _t_1);
        }
        r0 = _d_1;
        r1 = _ts_0;
        WL_JMP(FID_admission_lv_mark);
      }
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_grant_go_k300)
    WL_POPN(3);
    Term _f_1 = STK(0);
    u32 _l_2 = STK(1);
    Term _l_3 = STK(2);
    Term _t2_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _f_1;
      STK(1) = _l_2;
      STK(2) = _l_3;
      STK(3) = _t2_0;
      STK(4) = FID_admission_lv_grant_go_k301;
      WL_PUSHN(5);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_grant_go_k301, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _f_1;
      e.mem[_t_2 + 1] = _l_2;
      e.mem[_t_2 + 2] = _l_3;
      e.mem[_t_2 + 3] = _t2_0;
      WL_CONT = term_tsk(FID_admission_lv_grant_go_k301, _t_2);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_pick)) {
      u64 _t_3 = task_node(e, FID_admission_lv_pick, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _l_2;
      e.mem[_t_3 + 1] = _l_3;
      e.mem[_t_3 + 2] = _t2_0;
      return term_tsk(FID_admission_lv_pick, _t_3);
    }
    r0 = _l_2;
    r1 = _l_3;
    r2 = _t2_0;
    WL_JMP(FID_admission_lv_pick);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_grant_go_k301)
    WL_POPN(4);
    Term _f_2 = STK(0);
    u32 _l_4 = STK(1);
    Term _l_5 = STK(2);
    Term _t2_1 = STK(3);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_grant_go)) {
      u64 _t_4 = task_node(e, FID_admission_lv_grant_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _f_2;
      e.mem[_t_4 + 1] = _h_0;
      e.mem[_t_4 + 2] = _h_1;
      e.mem[_t_4 + 3] = _l_4;
      e.mem[_t_4 + 4] = _l_5;
      e.mem[_t_4 + 5] = _t2_1;
      return term_tsk(FID_admission_lv_grant_go, _t_4);
    }
    r0 = _f_2;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _l_4;
    r4 = _l_5;
    r5 = _t2_1;
    WL_JMP(FID_admission_lv_grant_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_drop)
    Term _ts_0 = r0;
    Term _k_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ts_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ts_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      u32 _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = _k_0;
        STK(4) = FID_admission_lv_drop_k303;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_admission_lv_drop_k303, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        e.mem[_t_0 + 3] = _k_0;
        WL_CONT = term_tsk(FID_admission_lv_drop_k303, _t_0);
        WL_IDX = 4;
      }
      r0 = _f_1;
      r1 = _k_0;
      _ts_0 = r0;
      _k_0 = r1;
      WL_AGAIN(FID_admission_lv_drop);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_drop_k303)
    WL_POPN(4);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    u32 _f_7 = STK(2);
    Term _k_1 = STK(3);
    Term _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_0(e, _o_0, _f_5, _k_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_126(e, _o_1, _v_0, _f_5, _f_6, _f_7, _h_0) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_set)
    Term _ts_0 = r0;
    Term _k_0 = r1;
    u32 _x_0 = r2;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ts_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ts_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      u32 _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = _k_0;
        STK(4) = _x_0;
        STK(5) = FID_admission_lv_set_k306;
        WL_PUSHN(6);
      } else {
        u64 _t_0 = task_node(e, FID_admission_lv_set_k306, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        e.mem[_t_0 + 3] = _k_0;
        e.mem[_t_0 + 4] = _x_0;
        WL_CONT = term_tsk(FID_admission_lv_set_k306, _t_0);
        WL_IDX = 5;
      }
      r0 = _f_1;
      r1 = _k_0;
      r2 = _x_0;
      _ts_0 = r0;
      _k_0 = r1;
      _x_0 = r2;
      WL_AGAIN(FID_admission_lv_set);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_set_k306)
    WL_POPN(5);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    u32 _f_7 = STK(2);
    Term _k_1 = STK(3);
    u32 _x_1 = STK(4);
    Term _h_0 = r0;
    WL_OPEN
    Term _v_0 = 0;
    u32 _v_1 = 0;
    u32 _v_2 = 0;
    u32 _v_3 = 0;
    Term _o_0[1];
    if (spin_0(e, _o_0, _f_5, _k_1) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_0[0];
    Term _o_1[3];
    if (spin_127(e, _o_1, _v_3, _f_5, _f_6, _f_7, _x_1) == 0) {
      return 0;
    }
    _v_0 = _o_1[0];
    _v_1 = (u32)_o_1[1];
    _v_2 = (u32)_o_1[2];
    u64 _nd_0 = heap_alloc(e, cls_fit(3));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, _v_1);
    e.mem[_nd_0 + 2] = rfc_seal(e, _v_2);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_0));
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_held)
    Term _ts_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _ts_0;
      STK(1) = FID_admission_lv_held_k308;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_admission_lv_held_k308, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _ts_0;
      WL_CONT = term_tsk(FID_admission_lv_held_k308, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_1 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = 0;
      e.mem[_t_1 + 1] = 0;
      e.mem[_t_1 + 2] = _ts_0;
      return term_tsk(FID_admission_lv_cnt, _t_1);
    }
    r0 = 0;
    r1 = 0;
    r2 = _ts_0;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_held_k308)
    WL_POPN(1);
    Term _ts_1 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_admission_lv_held_k309;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_held_k309, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_admission_lv_held_k309, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_3 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = 0;
      e.mem[_t_3 + 1] = 1;
      e.mem[_t_3 + 2] = _ts_1;
      return term_tsk(FID_admission_lv_cnt, _t_3);
    }
    r0 = 0;
    r1 = 1;
    r2 = _ts_1;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_held_k309)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    r0 = nat_chk(e, _h_2 + _h_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_cnt)
    u32 _m_0 = r0;
    u32 _c_0 = r1;
    Term _ts_0 = r2;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ts_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _ts_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      u32 _f_3 = e.mem[_sp_1 + 1];
      u32 _f_4 = e.mem[_sp_1 + 2];
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _m_0;
        STK(1) = _c_0;
        STK(2) = _f_2;
        STK(3) = _f_3;
        STK(4) = _f_4;
        STK(5) = FID_admission_lv_cnt_k314;
        WL_PUSHN(6);
      } else {
        u64 _t_0 = task_node(e, FID_admission_lv_cnt_k314, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _m_0;
        e.mem[_t_0 + 1] = _c_0;
        e.mem[_t_0 + 2] = _f_2;
        e.mem[_t_0 + 3] = _f_3;
        e.mem[_t_0 + 4] = _f_4;
        WL_CONT = term_tsk(FID_admission_lv_cnt_k314, _t_0);
        WL_IDX = 5;
      }
      r0 = _m_0;
      r1 = _c_0;
      r2 = _f_1;
      _m_0 = r0;
      _c_0 = r1;
      _ts_0 = r2;
      WL_AGAIN(FID_admission_lv_cnt);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_cnt_k314)
    WL_POPN(5);
    u32 _m_1 = STK(0);
    u32 _c_1 = STK(1);
    Term _f_5 = STK(2);
    u32 _f_6 = STK(3);
    u32 _f_7 = STK(4);
    Term _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_84(e, _o_0, _m_1, _c_1, _f_5, _f_6, _f_7) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    Term _o_1[1];
    if (spin_128(e, _o_1, _v_0, _h_0) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_preempt)
    Term _ts_0 = r0;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ts_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _ts_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      u32 _f_3 = e.mem[_sp_1 + 1];
      u32 _f_4 = e.mem[_sp_1 + 2];
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = FID_admission_lv_preempt_k320;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_admission_lv_preempt_k320, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        WL_CONT = term_tsk(FID_admission_lv_preempt_k320, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      _ts_0 = r0;
      WL_AGAIN(FID_admission_lv_preempt);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_preempt_k320)
    WL_POPN(3);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    u32 _f_7 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    Term _v_0 = 0;
    u32 _v_1 = 0;
    u32 _v_2 = 0;
    Term _o_2[3];
    if (spin_129(e, _o_2, _f_5, _f_6, _f_7) == 0) {
      return 0;
    }
    _v_0 = _o_2[0];
    _v_1 = (u32)_o_2[1];
    _v_2 = (u32)_o_2[2];
    u64 _nd_0 = heap_alloc(e, cls_fit(3));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_0);
    e.mem[_nd_0 + 1] = rfc_seal(e, _v_1);
    e.mem[_nd_0 + 2] = rfc_seal(e, _v_2);
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_admission_Lv, _nd_0));
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
        STK(1) = FID_List_append_k322;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_List_append_k322, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_List_append_k322, _t_0);
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
  WL_CASE(FID_List_append_k322)
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
  WL_CASE(FID_doc_seen_unseen)
    Term _seen_0 = r0;
    Term _ats_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ats_0) == CID_Nil) {
      r0 = term_pak(CID_Nil, 0);
      WL_RETN(1);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _ats_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _seen_0;
        STK(1) = _f_2;
        STK(2) = _f_3;
        STK(3) = _f_4;
        STK(4) = FID_doc_seen_unseen_k327;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_doc_seen_unseen_k327, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _seen_0;
        e.mem[_t_0 + 1] = _f_2;
        e.mem[_t_0 + 2] = _f_3;
        e.mem[_t_0 + 3] = _f_4;
        WL_CONT = term_tsk(FID_doc_seen_unseen_k327, _t_0);
        WL_IDX = 4;
      }
      r0 = _seen_0;
      r1 = _f_1;
      _seen_0 = r0;
      _ats_0 = r1;
      WL_AGAIN(FID_doc_seen_unseen);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_unseen_k327)
    WL_POPN(4);
    Term _seen_1 = STK(0);
    Term _f_5 = STK(1);
    u32 _f_6 = STK(2);
    Term _f_7 = STK(3);
    Term _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _v_1 = 0;
    Term _o_0[1];
    if (spin_91(e, _o_0, _f_5, _f_6, _f_7) == 0) {
      return 0;
    }
    _v_1 = _o_0[0];
    Term _o_2[1];
    if (spin_131(e, _o_2, _v_1, _seen_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_2[0];
    Term _o_3[1];
    if (spin_132(e, _o_3, _f_5, _f_6, _f_7, _h_0, _v_0) == 0) {
      return 0;
    }
    r0 = _o_3[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_6)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_6_k336;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_6_k336, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_6_k336, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_6)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_6, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _xs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_6, _t_1);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_6_k336)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[1];
    if (spin_82(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_5)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_5_k338;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_5_k338, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_5_k338, _t_0);
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
  WL_CASE(FID_wire_put_list_5_k338)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[1];
    if (spin_82(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_workflow_found)
    Term _rs_0 = r0;
    Term _k_0 = r1;
    Term _i_0 = r2;
    WL_OPEN
    WL_SPIN
    if (term_aux(_rs_0) == CID_Nil) {
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    } else {
      Term _fb_0[2];
      u64 _sp_0 = ctr_take(e, _rs_0, 2, _fb_0);
      Term _f_0 = _fb_0[0];
      Term _f_1 = _fb_0[1];
      Term _fb_1[2];
      u64 _sp_1 = ctr_take(e, _f_0, 2, _fb_1);
      Term _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _k_0;
        STK(3) = _i_0;
        STK(4) = FID_workflow_found_k349;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_workflow_found_k349, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _k_0;
        e.mem[_t_0 + 3] = _i_0;
        WL_CONT = term_tsk(FID_workflow_found_k349, _t_0);
        WL_IDX = 4;
      }
      r0 = _f_1;
      r1 = _k_0;
      r2 = nat_chk(e, _i_0 + 1);
      _rs_0 = r0;
      _k_0 = r1;
      _i_0 = r2;
      WL_AGAIN(FID_workflow_found);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_workflow_found_k349)
    WL_POPN(4);
    Term _f_4 = STK(0);
    u32 _f_5 = STK(1);
    Term _k_1 = STK(2);
    Term _i_1 = STK(3);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    u32 _v_1 = 0;
    Term _o_0[1];
    if (spin_0(e, _o_0, _k_1, _f_4) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_0[0];
    u32 _v_2 = 0;
    Term _o_1[1];
    if (spin_134(e, _o_1, _f_5) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_1[0];
    Term _o_2[1];
    if (spin_34(e, _o_2, _v_1, _v_2) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_2[0];
    Term _o_3[2];
    if (spin_135(e, _o_3, _v_0, _i_1, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = (u32)_o_3[0];
    r1 = _o_3[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_1)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_1_k357;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_1_k357, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_1_k357, _t_0);
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
  WL_CASE(FID_wire_get_list_1_k357)
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
          STK(1) = FID_wire_get_list_1_k358;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_1_k358, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_1_k358, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_key)) {
          u64 _t_3 = task_node(e, FID_ffi_aux_fallback_get_key, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_aux_fallback_get_key, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_aux_fallback_get_key);
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
  WL_CASE(FID_wire_get_list_1_k358)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_1)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      e.mem[_t_4 + 5] = _h_7;
      return term_tsk(FID_wire_get_list_go_1, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    WL_JMP(FID_wire_get_list_go_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_look)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_aux_fallback_get_look_k365;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_aux_fallback_get_look_k365, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_aux_fallback_get_look_k365, _t_0);
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
  WL_CASE(FID_ffi_aux_fallback_get_look_k365)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_look_k366;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_aux_fallback_get_look_k366, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_look_k366, _t_2);
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
          STK(0) = FID_ffi_aux_fallback_get_look_k367;
          WL_PUSHN(1);
        } else {
          u64 _t_4 = task_node(e, FID_ffi_aux_fallback_get_look_k367, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_look_k367, _t_4);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_5);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else {
        Term _b_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_aux_fallback_get_look_k366)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_99(e, _o_0, _h_3, _h_4, _h_5, 0) == 0) {
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
  WL_CASE(FID_ffi_aux_fallback_get_look_k367)
    u32 _h_6 = r0;
    Term _h_7 = r1;
    Term _h_8 = r2;
    WL_OPEN
    Term _o_1[4];
    if (spin_99(e, _o_1, _h_6, _h_7, _h_8, 1ull) == 0) {
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
  WL_CASE(FID_ffi_aux_fallback_get_sel)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_aux_fallback_get_sel_k371;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_aux_fallback_get_sel_k371, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_aux_fallback_get_sel_k371, _t_0);
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
  WL_CASE(FID_ffi_aux_fallback_get_sel_k371)
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
        r0 = 0;
        r1 = 1;
        r2 = 0;
        r3 = _h_2;
        WL_RETN(4);
      } else if (_h_1 == 2) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_sel_k372;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_aux_fallback_get_sel_k372, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_sel_k372, _t_2);
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
        Term _c_0 = (_h_1 - 3);
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
  WL_CASE(FID_ffi_aux_fallback_get_sel_k372)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_67(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_aux_fallback_listed)
    Term _ks_0 = r0;
    Term _k_0 = r1;
    Term _k_1 = r2;
    Term _k_2 = r3;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ks_0) == CID_Nil) {
      r0 = 0;
      WL_RETN(1);
    } else {
      u64 _sp_0 = term_peek(e.mem, _ks_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      Term _f_3 = e.mem[_sp_1 + 1];
      Term _f_4 = e.mem[_sp_1 + 2];
      if (seq) {
        WL_ROOM(7, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = _f_4;
        STK(3) = _k_0;
        STK(4) = _k_1;
        STK(5) = _k_2;
        STK(6) = FID_aux_fallback_listed_k376;
        WL_PUSHN(7);
      } else {
        u64 _t_0 = task_node(e, FID_aux_fallback_listed_k376, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        e.mem[_t_0 + 2] = _f_4;
        e.mem[_t_0 + 3] = _k_0;
        e.mem[_t_0 + 4] = _k_1;
        e.mem[_t_0 + 5] = _k_2;
        WL_CONT = term_tsk(FID_aux_fallback_listed_k376, _t_0);
        WL_IDX = 6;
      }
      r0 = _f_1;
      r1 = _k_0;
      r2 = _k_1;
      r3 = _k_2;
      _ks_0 = r0;
      _k_0 = r1;
      _k_1 = r2;
      _k_2 = r3;
      WL_AGAIN(FID_aux_fallback_listed);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_aux_fallback_listed_k376)
    WL_POPN(6);
    Term _f_5 = STK(0);
    Term _f_6 = STK(1);
    Term _f_7 = STK(2);
    Term _k_3 = STK(3);
    Term _k_4 = STK(4);
    Term _k_5 = STK(5);
    u32 _h_0 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_5[1];
    if (spin_140(e, _o_5, _f_5, _f_6, _f_7, _k_3, _k_4, _k_5) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_5[0];
    r0 = ((_v_0) | (_h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_1)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_1_k379;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_1_k379, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_1_k379, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_1)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_go_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _xs_0;
      e.mem[_t_1 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_1, _t_1);
    }
    r0 = _xs_0;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_1_k379)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[1];
    if (spin_82(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_6)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_6_k401;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_6_k401, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_6_k401, _t_0);
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
  WL_CASE(FID_wire_get_list_6_k401)
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
          STK(1) = FID_wire_get_list_6_k402;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_6_k402, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_6_k402, _t_2);
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
  WL_CASE(FID_wire_get_list_6_k402)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_6)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_6, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      return term_tsk(FID_wire_get_list_go_6, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    WL_JMP(FID_wire_get_list_go_6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_4)
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
      u32 _f_2 = _fb_1[0];
      Term _f_3 = _fb_1[1];
      spare_free(e, cls_fit(2), _sp_1);
      spare_free(e, cls_fit(2), _sp_0);
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _f_2;
        STK(1) = _f_3;
        STK(2) = FID_wire_put_list_go_4_k413;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_wire_put_list_go_4_k413, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_3;
        WL_CONT = term_tsk(FID_wire_put_list_go_4_k413, _t_0);
        WL_IDX = 2;
      }
      r0 = _f_1;
      r1 = _rest_0;
      _xs_0 = r0;
      _rest_0 = r1;
      WL_AGAIN(FID_wire_put_list_go_4);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_go_4_k413)
    WL_POPN(2);
    u32 _f_4 = STK(0);
    Term _f_5 = STK(1);
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_152(e, _o_1, _f_4, _f_5, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_maybe_nat)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_maybe_nat_k425;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_maybe_nat_k425, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_maybe_nat_k425, _t_0);
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
  WL_CASE(FID_ffi_child_get_maybe_nat_k425)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _h_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      if (_v_0 == 0) {
        r0 = 0;
        r1 = 0;
        r2 = 0;
        r3 = _h_2;
        WL_RETN(4);
      } else if (_v_0 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_child_get_maybe_nat_k426;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_child_get_maybe_nat_k426, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_child_get_maybe_nat_k426, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_v_0 == 2) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      } else if (_v_0 == 3) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      } else if (_v_0 == 4) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      } else {
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
  WL_CASE(FID_ffi_child_get_maybe_nat_k426)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_1[4];
    if (spin_75(e, _o_1, _h_3, _h_4, _h_5) == 0) {
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
        STK(1) = FID_wire_value_k436;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_value_k436, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_wire_value_k436, _t_0);
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
  WL_CASE(FID_wire_value_k436)
    WL_POPN(1);
    Term _f_2 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    r0 = nat_chk(e, _f_2 + nat_mul(e, 10ull, _h_0));
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_get_cls)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_admission_get_cls_k455;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_admission_get_cls_k455, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_admission_get_cls_k455, _t_0);
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
  WL_CASE(FID_ffi_admission_get_cls_k455)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_1[3];
    if (spin_162(e, _o_1, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_put_list_0)
    Term _xs_0 = r0;
    Term _rest_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_put_list_0_k458;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_put_list_0_k458, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_put_list_0_k458, _t_0);
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
  WL_CASE(FID_wire_put_list_0_k458)
    Term _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[1];
    if (spin_82(e, _o_0, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_grant)
    u32 _l_0 = r0;
    Term _l_1 = r1;
    Term _ts_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _l_0;
      STK(1) = _l_1;
      STK(2) = _ts_0;
      STK(3) = FID_admission_lv_grant_k461;
      WL_PUSHN(4);
    } else {
      u64 _t_0 = task_node(e, FID_admission_lv_grant_k461, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _l_0;
      e.mem[_t_0 + 1] = _l_1;
      e.mem[_t_0 + 2] = _ts_0;
      WL_CONT = term_tsk(FID_admission_lv_grant_k461, _t_0);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_waits)) {
      u64 _t_1 = task_node(e, FID_admission_lv_waits, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _ts_0;
      return term_tsk(FID_admission_lv_waits, _t_1);
    }
    r0 = _ts_0;
    WL_JMP(FID_admission_lv_waits);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_grant_k461)
    WL_POPN(3);
    u32 _l_2 = STK(0);
    Term _l_3 = STK(1);
    Term _ts_1 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _l_2;
      STK(1) = _l_3;
      STK(2) = _ts_1;
      STK(3) = _h_0;
      STK(4) = FID_admission_lv_grant_k462;
      WL_PUSHN(5);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_grant_k462, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _l_2;
      e.mem[_t_2 + 1] = _l_3;
      e.mem[_t_2 + 2] = _ts_1;
      e.mem[_t_2 + 3] = _h_0;
      WL_CONT = term_tsk(FID_admission_lv_grant_k462, _t_2);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_pick)) {
      u64 _t_3 = task_node(e, FID_admission_lv_pick, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _l_2;
      e.mem[_t_3 + 1] = _l_3;
      e.mem[_t_3 + 2] = _ts_1;
      return term_tsk(FID_admission_lv_pick, _t_3);
    }
    r0 = _l_2;
    r1 = _l_3;
    r2 = _ts_1;
    WL_JMP(FID_admission_lv_pick);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_grant_k462)
    WL_POPN(4);
    u32 _l_4 = STK(0);
    Term _l_5 = STK(1);
    Term _ts_2 = STK(2);
    Term _h_3 = STK(3);
    u32 _h_1 = r0;
    u32 _h_2 = r1;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_grant_go)) {
      u64 _t_4 = task_node(e, FID_admission_lv_grant_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _h_3;
      e.mem[_t_4 + 1] = _h_1;
      e.mem[_t_4 + 2] = _h_2;
      e.mem[_t_4 + 3] = _l_4;
      e.mem[_t_4 + 4] = _l_5;
      e.mem[_t_4 + 5] = _ts_2;
      return term_tsk(FID_admission_lv_grant_go, _t_4);
    }
    r0 = _h_3;
    r1 = _h_1;
    r2 = _h_2;
    r3 = _l_4;
    r4 = _l_5;
    r5 = _ts_2;
    WL_JMP(FID_admission_lv_grant_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_leave)
    u32 _m_0 = r0;
    u32 _m_1 = r1;
    u32 _l_0 = r2;
    Term _l_1 = r3;
    Term _ts_0 = r4;
    Term _k_0 = r5;
    WL_OPEN
    if (_m_0 == 1) {
      if (_m_1 == 0) {
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _l_0;
          STK(1) = _l_1;
          STK(2) = FID_admission_lv_leave_k464;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_admission_lv_leave_k464, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _l_0;
          e.mem[_t_0 + 1] = _l_1;
          WL_CONT = term_tsk(FID_admission_lv_leave_k464, _t_0);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_drop)) {
          u64 _t_1 = task_node(e, FID_admission_lv_drop, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _ts_0;
          e.mem[_t_1 + 1] = _k_0;
          return term_tsk(FID_admission_lv_drop, _t_1);
        }
        r0 = _ts_0;
        r1 = _k_0;
        WL_JMP(FID_admission_lv_drop);
      } else if (_m_1 == 1) {
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _l_0;
          STK(1) = _l_1;
          STK(2) = FID_admission_lv_leave_k465;
          WL_PUSHN(3);
        } else {
          u64 _t_3 = task_node(e, FID_admission_lv_leave_k465, WL_CONT, WL_IDX, 1);
          e.mem[_t_3 + 0] = _l_0;
          e.mem[_t_3 + 1] = _l_1;
          WL_CONT = term_tsk(FID_admission_lv_leave_k465, _t_3);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_drop)) {
          u64 _t_4 = task_node(e, FID_admission_lv_drop, WL_CONT, WL_IDX, 0);
          e.mem[_t_4 + 0] = _ts_0;
          e.mem[_t_4 + 1] = _k_0;
          return term_tsk(FID_admission_lv_drop, _t_4);
        }
        r0 = _ts_0;
        r1 = _k_0;
        WL_JMP(FID_admission_lv_drop);
      } else if (_m_1 == 2) {
        r0 = _ts_0;
        WL_RETN(1);
      } else if (_m_1 == 3) {
        r0 = _ts_0;
        WL_RETN(1);
      } else {
        r0 = _ts_0;
        WL_RETN(1);
      }
    } else {
      r0 = _ts_0;
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_leave_k464)
    WL_POPN(2);
    u32 _l_2 = STK(0);
    Term _l_3 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_grant)) {
      u64 _t_2 = task_node(e, FID_admission_lv_grant, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _l_2;
      e.mem[_t_2 + 1] = _l_3;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_admission_lv_grant, _t_2);
    }
    r0 = _l_2;
    r1 = _l_3;
    r2 = _h_0;
    WL_JMP(FID_admission_lv_grant);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_leave_k465)
    WL_POPN(2);
    u32 _l_4 = STK(0);
    Term _l_5 = STK(1);
    Term _h_1 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_grant)) {
      u64 _t_5 = task_node(e, FID_admission_lv_grant, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _l_4;
      e.mem[_t_5 + 1] = _l_5;
      e.mem[_t_5 + 2] = _h_1;
      return term_tsk(FID_admission_lv_grant, _t_5);
    }
    r0 = _l_4;
    r1 = _l_5;
    r2 = _h_1;
    WL_JMP(FID_admission_lv_grant);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_release)
    u32 _m_0 = r0;
    u32 _m_1 = r1;
    u32 _l_0 = r2;
    Term _l_1 = r3;
    Term _ts_0 = r4;
    Term _k_0 = r5;
    WL_OPEN
    if (_m_0 == 1) {
      if (_m_1 == 2) {
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _l_0;
          STK(1) = _l_1;
          STK(2) = FID_admission_lv_release_k467;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_admission_lv_release_k467, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _l_0;
          e.mem[_t_0 + 1] = _l_1;
          WL_CONT = term_tsk(FID_admission_lv_release_k467, _t_0);
          WL_IDX = 2;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_drop)) {
          u64 _t_1 = task_node(e, FID_admission_lv_drop, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _ts_0;
          e.mem[_t_1 + 1] = _k_0;
          return term_tsk(FID_admission_lv_drop, _t_1);
        }
        r0 = _ts_0;
        r1 = _k_0;
        WL_JMP(FID_admission_lv_drop);
      } else if (_m_1 == 3) {
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_drop)) {
          u64 _t_3 = task_node(e, FID_admission_lv_drop, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _ts_0;
          e.mem[_t_3 + 1] = _k_0;
          return term_tsk(FID_admission_lv_drop, _t_3);
        }
        r0 = _ts_0;
        r1 = _k_0;
        WL_JMP(FID_admission_lv_drop);
      } else if (_m_1 == 0) {
        r0 = _ts_0;
        WL_RETN(1);
      } else if (_m_1 == 1) {
        r0 = _ts_0;
        WL_RETN(1);
      } else {
        r0 = _ts_0;
        WL_RETN(1);
      }
    } else {
      r0 = _ts_0;
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_release_k467)
    WL_POPN(2);
    u32 _l_2 = STK(0);
    Term _l_3 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_grant)) {
      u64 _t_2 = task_node(e, FID_admission_lv_grant, WL_CONT, WL_IDX, 0);
      e.mem[_t_2 + 0] = _l_2;
      e.mem[_t_2 + 1] = _l_3;
      e.mem[_t_2 + 2] = _h_0;
      return term_tsk(FID_admission_lv_grant, _t_2);
    }
    r0 = _l_2;
    r1 = _l_3;
    r2 = _h_0;
    WL_JMP(FID_admission_lv_grant);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_find)
    Term _ts_0 = r0;
    Term _k_0 = r1;
    WL_OPEN
    WL_SPIN
    if (term_aux(_ts_0) == CID_Nil) {
      r0 = 0;
      r1 = 0;
      WL_RETN(2);
    } else {
      u64 _sp_0 = term_peek(e.mem, _ts_0);
      Term _f_0 = e.mem[_sp_0 + 0];
      Term _f_1 = e.mem[_sp_0 + 1];
      u64 _sp_1 = term_peek(e.mem, _f_0);
      Term _f_2 = e.mem[_sp_1 + 0];
      u32 _f_3 = e.mem[_sp_1 + 1];
      u32 _f_4 = e.mem[_sp_1 + 2];
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _f_2;
        STK(1) = _f_4;
        STK(2) = _k_0;
        STK(3) = FID_admission_lv_find_k469;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_admission_lv_find_k469, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_2;
        e.mem[_t_0 + 1] = _f_4;
        e.mem[_t_0 + 2] = _k_0;
        WL_CONT = term_tsk(FID_admission_lv_find_k469, _t_0);
        WL_IDX = 3;
      }
      r0 = _f_1;
      r1 = _k_0;
      _ts_0 = r0;
      _k_0 = r1;
      WL_AGAIN(FID_admission_lv_find);
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_find_k469)
    WL_POPN(3);
    Term _f_5 = STK(0);
    u32 _f_6 = STK(1);
    Term _k_1 = STK(2);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_0(e, _o_0, _f_5, _k_1) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    Term _o_1[2];
    if (spin_163(e, _o_1, _v_0, _f_6, _h_0, _h_1) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_collect)
    u32 _m_0 = r0;
    u32 _m_1 = r1;
    Term _ts_0 = r2;
    Term _k_0 = r3;
    WL_OPEN
    if (_m_0 == 1) {
      if (_m_1 == 1) {
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_set)) {
          u64 _t_0 = task_node(e, FID_admission_lv_set, WL_CONT, WL_IDX, 0);
          e.mem[_t_0 + 0] = _ts_0;
          e.mem[_t_0 + 1] = _k_0;
          e.mem[_t_0 + 2] = 2;
          return term_tsk(FID_admission_lv_set, _t_0);
        }
        r0 = _ts_0;
        r1 = _k_0;
        r2 = 2;
        WL_JMP(FID_admission_lv_set);
      } else if (_m_1 == 0) {
        r0 = _ts_0;
        WL_RETN(1);
      } else if (_m_1 == 2) {
        r0 = _ts_0;
        WL_RETN(1);
      } else if (_m_1 == 3) {
        r0 = _ts_0;
        WL_RETN(1);
      } else {
        r0 = _ts_0;
        WL_RETN(1);
      }
    } else {
      r0 = _ts_0;
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_bg)
    u32 _l_0 = r0;
    Term _l_1 = r1;
    Term _ts_0 = r2;
    Term _k_0 = r3;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _l_0;
      STK(1) = _l_1;
      STK(2) = _ts_0;
      STK(3) = _k_0;
      STK(4) = FID_admission_lv_admit_bg_k472;
      WL_PUSHN(5);
    } else {
      u64 _t_0 = task_node(e, FID_admission_lv_admit_bg_k472, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _l_0;
      e.mem[_t_0 + 1] = _l_1;
      e.mem[_t_0 + 2] = _ts_0;
      e.mem[_t_0 + 3] = _k_0;
      WL_CONT = term_tsk(FID_admission_lv_admit_bg_k472, _t_0);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_1 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = 0;
      e.mem[_t_1 + 1] = 0;
      e.mem[_t_1 + 2] = _ts_0;
      return term_tsk(FID_admission_lv_cnt, _t_1);
    }
    r0 = 0;
    r1 = 0;
    r2 = _ts_0;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_bg_k472)
    WL_POPN(4);
    u32 _l_2 = STK(0);
    Term _l_3 = STK(1);
    Term _ts_1 = STK(2);
    Term _k_1 = STK(3);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _l_2;
      STK(1) = _l_3;
      STK(2) = _ts_1;
      STK(3) = _k_1;
      STK(4) = _h_0;
      STK(5) = FID_admission_lv_admit_bg_k473;
      WL_PUSHN(6);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_admit_bg_k473, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _l_2;
      e.mem[_t_2 + 1] = _l_3;
      e.mem[_t_2 + 2] = _ts_1;
      e.mem[_t_2 + 3] = _k_1;
      e.mem[_t_2 + 4] = _h_0;
      WL_CONT = term_tsk(FID_admission_lv_admit_bg_k473, _t_2);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_3 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = 1;
      e.mem[_t_3 + 1] = 0;
      e.mem[_t_3 + 2] = _ts_1;
      return term_tsk(FID_admission_lv_cnt, _t_3);
    }
    r0 = 1;
    r1 = 0;
    r2 = _ts_1;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_bg_k473)
    WL_POPN(5);
    u32 _l_4 = STK(0);
    Term _l_5 = STK(1);
    Term _ts_2 = STK(2);
    Term _k_2 = STK(3);
    Term _h_2 = STK(4);
    Term _h_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(7, 0);
      STK(0) = _l_4;
      STK(1) = _l_5;
      STK(2) = _ts_2;
      STK(3) = _k_2;
      STK(4) = _h_2;
      STK(5) = _h_1;
      STK(6) = FID_admission_lv_admit_bg_k474;
      WL_PUSHN(7);
    } else {
      u64 _t_4 = task_node(e, FID_admission_lv_admit_bg_k474, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _l_4;
      e.mem[_t_4 + 1] = _l_5;
      e.mem[_t_4 + 2] = _ts_2;
      e.mem[_t_4 + 3] = _k_2;
      e.mem[_t_4 + 4] = _h_2;
      e.mem[_t_4 + 5] = _h_1;
      WL_CONT = term_tsk(FID_admission_lv_admit_bg_k474, _t_4);
      WL_IDX = 6;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_5 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = 1;
      e.mem[_t_5 + 1] = 1;
      e.mem[_t_5 + 2] = _ts_2;
      return term_tsk(FID_admission_lv_cnt, _t_5);
    }
    r0 = 1;
    r1 = 1;
    r2 = _ts_2;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_bg_k474)
    WL_POPN(6);
    u32 _l_6 = STK(0);
    Term _l_7 = STK(1);
    Term _ts_3 = STK(2);
    Term _k_3 = STK(3);
    Term _h_4 = STK(4);
    Term _h_5 = STK(5);
    Term _h_3 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(8, 0);
      STK(0) = _l_6;
      STK(1) = _l_7;
      STK(2) = _ts_3;
      STK(3) = _k_3;
      STK(4) = _h_4;
      STK(5) = _h_5;
      STK(6) = _h_3;
      STK(7) = FID_admission_lv_admit_bg_k475;
      WL_PUSHN(8);
    } else {
      u64 _t_6 = task_node(e, FID_admission_lv_admit_bg_k475, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _l_6;
      e.mem[_t_6 + 1] = _l_7;
      e.mem[_t_6 + 2] = _ts_3;
      e.mem[_t_6 + 3] = _k_3;
      e.mem[_t_6 + 4] = _h_4;
      e.mem[_t_6 + 5] = _h_5;
      e.mem[_t_6 + 6] = _h_3;
      WL_CONT = term_tsk(FID_admission_lv_admit_bg_k475, _t_6);
      WL_IDX = 7;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_held)) {
      u64 _t_7 = task_node(e, FID_admission_lv_held, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _ts_3;
      return term_tsk(FID_admission_lv_held, _t_7);
    }
    r0 = _ts_3;
    WL_JMP(FID_admission_lv_held);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_bg_k475)
    WL_POPN(7);
    u32 _l_8 = STK(0);
    Term _l_9 = STK(1);
    Term _ts_4 = STK(2);
    Term _k_4 = STK(3);
    Term _h_7 = STK(4);
    Term _h_8 = STK(5);
    Term _h_9 = STK(6);
    Term _h_6 = r0;
    WL_OPEN
    Term _v_0 = 0;
    u32 _v_1 = 0;
    u32 _v_2 = 0;
    u32 _v_3 = 0;
    Term _o_0[1];
    if (spin_164(e, _o_0, _h_7) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_0[0];
    u32 _v_4 = 0;
    u32 _v_5 = 0;
    Term _o_1[1];
    if (spin_164(e, _o_1, _h_8) == 0) {
      return 0;
    }
    _v_5 = (u32)_o_1[0];
    u32 _v_6 = 0;
    u32 _v_7 = 0;
    Term _o_2[1];
    if (spin_164(e, _o_2, _h_9) == 0) {
      return 0;
    }
    _v_7 = (u32)_o_2[0];
    u32 _v_8 = 0;
    Term _o_3[1];
    if (spin_123(e, _o_3, _l_8, _l_9, _h_6) == 0) {
      return 0;
    }
    _v_8 = (u32)_o_3[0];
    Term _o_4[1];
    if (spin_34(e, _o_4, _v_7, _v_8) == 0) {
      return 0;
    }
    _v_6 = (u32)_o_4[0];
    Term _o_5[1];
    if (spin_34(e, _o_5, _v_5, _v_6) == 0) {
      return 0;
    }
    _v_4 = (u32)_o_5[0];
    Term _o_6[1];
    if (spin_34(e, _o_6, _v_3, _v_4) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_6[0];
    Term _o_7[1];
    if (spin_165(e, _o_7, _v_2) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_7[0];
    Term _o_8[1];
    if (spin_166(e, _o_8, _v_1, _k_4, 1) == 0) {
      return 0;
    }
    _v_0 = _o_8[0];
    if (!DEVICE && !seq && fid_nofk(FID_List_append)) {
      u64 _t_8 = task_node(e, FID_List_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_8 + 0] = _ts_4;
      e.mem[_t_8 + 1] = _v_0;
      return term_tsk(FID_List_append, _t_8);
    }
    r0 = _ts_4;
    r1 = _v_0;
    WL_JMP(FID_List_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_ia)
    u32 _l_0 = r0;
    Term _l_1 = r1;
    Term _q_0 = r2;
    Term _ts_0 = r3;
    Term _k_0 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _l_0;
      STK(1) = _l_1;
      STK(2) = _q_0;
      STK(3) = _ts_0;
      STK(4) = _k_0;
      STK(5) = FID_admission_lv_admit_ia_k477;
      WL_PUSHN(6);
    } else {
      u64 _t_0 = task_node(e, FID_admission_lv_admit_ia_k477, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _l_0;
      e.mem[_t_0 + 1] = _l_1;
      e.mem[_t_0 + 2] = _q_0;
      e.mem[_t_0 + 3] = _ts_0;
      e.mem[_t_0 + 4] = _k_0;
      WL_CONT = term_tsk(FID_admission_lv_admit_ia_k477, _t_0);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_preempt)) {
      u64 _t_1 = task_node(e, FID_admission_lv_preempt, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _ts_0;
      return term_tsk(FID_admission_lv_preempt, _t_1);
    }
    r0 = _ts_0;
    WL_JMP(FID_admission_lv_preempt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_ia_k477)
    WL_POPN(5);
    u32 _l_2 = STK(0);
    Term _l_3 = STK(1);
    Term _q_1 = STK(2);
    Term _ts_1 = STK(3);
    Term _k_1 = STK(4);
    Term _h_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(7, 0);
      STK(0) = _l_2;
      STK(1) = _l_3;
      STK(2) = _q_1;
      STK(3) = _ts_1;
      STK(4) = _k_1;
      STK(5) = _h_0;
      STK(6) = FID_admission_lv_admit_ia_k478;
      WL_PUSHN(7);
    } else {
      u64 _t_2 = task_node(e, FID_admission_lv_admit_ia_k478, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _l_2;
      e.mem[_t_2 + 1] = _l_3;
      e.mem[_t_2 + 2] = _q_1;
      e.mem[_t_2 + 3] = _ts_1;
      e.mem[_t_2 + 4] = _k_1;
      e.mem[_t_2 + 5] = _h_0;
      WL_CONT = term_tsk(FID_admission_lv_admit_ia_k478, _t_2);
      WL_IDX = 6;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_3 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = 1;
      e.mem[_t_3 + 1] = 0;
      e.mem[_t_3 + 2] = _ts_1;
      return term_tsk(FID_admission_lv_cnt, _t_3);
    }
    r0 = 1;
    r1 = 0;
    r2 = _ts_1;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_ia_k478)
    WL_POPN(6);
    u32 _l_4 = STK(0);
    Term _l_5 = STK(1);
    Term _q_2 = STK(2);
    Term _ts_2 = STK(3);
    Term _k_2 = STK(4);
    Term _h_2 = STK(5);
    Term _h_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(8, 0);
      STK(0) = _l_4;
      STK(1) = _l_5;
      STK(2) = _q_2;
      STK(3) = _ts_2;
      STK(4) = _k_2;
      STK(5) = _h_2;
      STK(6) = _h_1;
      STK(7) = FID_admission_lv_admit_ia_k479;
      WL_PUSHN(8);
    } else {
      u64 _t_4 = task_node(e, FID_admission_lv_admit_ia_k479, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _l_4;
      e.mem[_t_4 + 1] = _l_5;
      e.mem[_t_4 + 2] = _q_2;
      e.mem[_t_4 + 3] = _ts_2;
      e.mem[_t_4 + 4] = _k_2;
      e.mem[_t_4 + 5] = _h_2;
      e.mem[_t_4 + 6] = _h_1;
      WL_CONT = term_tsk(FID_admission_lv_admit_ia_k479, _t_4);
      WL_IDX = 7;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_5 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = 0;
      e.mem[_t_5 + 1] = 0;
      e.mem[_t_5 + 2] = _ts_2;
      return term_tsk(FID_admission_lv_cnt, _t_5);
    }
    r0 = 0;
    r1 = 0;
    r2 = _ts_2;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_ia_k479)
    WL_POPN(7);
    u32 _l_6 = STK(0);
    Term _l_7 = STK(1);
    Term _q_3 = STK(2);
    Term _ts_3 = STK(3);
    Term _k_3 = STK(4);
    Term _h_4 = STK(5);
    Term _h_5 = STK(6);
    Term _h_3 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(9, 0);
      STK(0) = _l_6;
      STK(1) = _l_7;
      STK(2) = _q_3;
      STK(3) = _ts_3;
      STK(4) = _k_3;
      STK(5) = _h_4;
      STK(6) = _h_5;
      STK(7) = _h_3;
      STK(8) = FID_admission_lv_admit_ia_k480;
      WL_PUSHN(9);
    } else {
      u64 _t_6 = task_node(e, FID_admission_lv_admit_ia_k480, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _l_6;
      e.mem[_t_6 + 1] = _l_7;
      e.mem[_t_6 + 2] = _q_3;
      e.mem[_t_6 + 3] = _ts_3;
      e.mem[_t_6 + 4] = _k_3;
      e.mem[_t_6 + 5] = _h_4;
      e.mem[_t_6 + 6] = _h_5;
      e.mem[_t_6 + 7] = _h_3;
      WL_CONT = term_tsk(FID_admission_lv_admit_ia_k480, _t_6);
      WL_IDX = 8;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_cnt)) {
      u64 _t_7 = task_node(e, FID_admission_lv_cnt, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = 1;
      e.mem[_t_7 + 1] = 0;
      e.mem[_t_7 + 2] = _ts_3;
      return term_tsk(FID_admission_lv_cnt, _t_7);
    }
    r0 = 1;
    r1 = 0;
    r2 = _ts_3;
    WL_JMP(FID_admission_lv_cnt);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_lv_admit_ia_k480)
    WL_POPN(8);
    u32 _l_8 = STK(0);
    Term _l_9 = STK(1);
    Term _q_4 = STK(2);
    Term _ts_4 = STK(3);
    Term _k_4 = STK(4);
    Term _h_7 = STK(5);
    Term _h_8 = STK(6);
    Term _h_9 = STK(7);
    Term _h_6 = r0;
    WL_OPEN
    term_sink(e, _ts_4);
    Term _v_0 = 0;
    u32 _v_1 = 0;
    u32 _v_2 = 0;
    u32 _v_3 = 0;
    Term _o_0[1];
    if (spin_164(e, _o_0, _h_8) == 0) {
      return 0;
    }
    _v_3 = (u32)_o_0[0];
    u32 _v_4 = 0;
    Term _o_1[1];
    if (spin_123(e, _o_1, _l_8, _l_9, _h_9) == 0) {
      return 0;
    }
    _v_4 = (u32)_o_1[0];
    Term _o_2[1];
    if (spin_34(e, _o_2, _v_3, _v_4) == 0) {
      return 0;
    }
    _v_2 = (u32)_o_2[0];
    u32 _v_5 = 0;
    Term _o_3[1];
    if (spin_124(e, _o_3, _q_4, _h_6) == 0) {
      return 0;
    }
    _v_5 = (u32)_o_3[0];
    Term _o_4[1];
    if (spin_167(e, _o_4, _v_2, _v_5) == 0) {
      return 0;
    }
    _v_1 = (u32)_o_4[0];
    Term _o_5[1];
    if (spin_166(e, _o_5, _v_1, _k_4, 0) == 0) {
      return 0;
    }
    _v_0 = _o_5[0];
    if (!DEVICE && !seq && fid_nofk(FID_List_append)) {
      u64 _t_8 = task_node(e, FID_List_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_8 + 0] = _h_7;
      e.mem[_t_8 + 1] = _v_0;
      return term_tsk(FID_List_append, _t_8);
    }
    r0 = _h_7;
    r1 = _v_0;
    WL_JMP(FID_List_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_doc_seen_get_at)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_doc_seen_get_at_k484;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_doc_seen_get_at_k484, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_doc_seen_get_at_k484, _t_0);
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
  WL_CASE(FID_ffi_doc_seen_get_at_k484)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_doc_seen_get_at_k485;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_doc_seen_get_at_k485, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_doc_seen_get_at_k485, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_seen_get_mnat)) {
        u64 _t_3 = task_node(e, FID_ffi_doc_seen_get_mnat, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_doc_seen_get_mnat, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_doc_seen_get_mnat);
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
  WL_CASE(FID_ffi_doc_seen_get_at_k485)
    WL_POPN(1);
    Term _h_7 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    Term _o_0[5];
    if (spin_130(e, _o_0, _h_7, _h_3, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = (u32)_o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_4)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    Term _cur_1 = r2;
    u32 _cur_2 = r3;
    Term _cur_3 = r4;
    Term _cur_4 = r5;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(3));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        e.mem[_nd_0 + 2] = rfc_seal(e, _cur_3);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_doc_seen_At, _nd_0));
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
          STK(4) = FID_wire_get_list_go_4_k487;
          WL_PUSHN(5);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_4_k487, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          e.mem[_t_0 + 3] = _cur_3;
          WL_CONT = term_tsk(FID_wire_get_list_go_4_k487, _t_0);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_seen_get_at)) {
          u64 _t_1 = task_node(e, FID_ffi_doc_seen_get_at, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_4;
          return term_tsk(FID_ffi_doc_seen_get_at, _t_1);
        }
        r0 = _cur_4;
        WL_JMP(FID_ffi_doc_seen_get_at);
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
  WL_CASE(FID_wire_get_list_go_4_k487)
    WL_POPN(4);
    Term _m_1 = STK(0);
    Term _cur_5 = STK(1);
    u32 _cur_6 = STK(2);
    Term _cur_7 = STK(3);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    u32 _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _cur_5;
      STK(1) = _cur_6;
      STK(2) = _cur_7;
      STK(3) = FID_wire_get_list_go_4_k488;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_4_k488, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_5;
      e.mem[_t_2 + 1] = _cur_6;
      e.mem[_t_2 + 2] = _cur_7;
      WL_CONT = term_tsk(FID_wire_get_list_go_4_k488, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_4)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_4, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      e.mem[_t_3 + 5] = _h_4;
      return term_tsk(FID_wire_get_list_go_4, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    r5 = _h_4;
    WL_JMP(FID_wire_get_list_go_4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_4_k488)
    WL_POPN(3);
    Term _cur_8 = STK(0);
    u32 _cur_9 = STK(1);
    Term _cur_10 = STK(2);
    u32 _h_5 = r0;
    Term _h_6 = r1;
    Term _h_7 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_169(e, _o_0, _cur_8, _cur_9, _cur_10, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check)
    Term _seen_0 = r0;
    Term _ats_0 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _seen_0;
      STK(1) = FID_doc_seen_check_k490;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_doc_seen_check_k490, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _seen_0;
      WL_CONT = term_tsk(FID_doc_seen_check_k490, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_doc_seen_unseen)) {
      u64 _t_1 = task_node(e, FID_doc_seen_unseen, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _seen_0;
      e.mem[_t_1 + 1] = _ats_0;
      return term_tsk(FID_doc_seen_unseen, _t_1);
    }
    r0 = _seen_0;
    r1 = _ats_0;
    WL_JMP(FID_doc_seen_unseen);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check_k490)
    WL_POPN(1);
    Term _seen_1 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    term_sink(e, _seen_1);
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_0;
      STK(1) = FID_doc_seen_check_k491;
      WL_PUSHN(2);
    } else {
      u64 _t_2 = task_node(e, FID_doc_seen_check_k491, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _h_0;
      WL_CONT = term_tsk(FID_doc_seen_check_k491, _t_2);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_doc_seen_lines)) {
      u64 _t_3 = task_node(e, FID_doc_seen_lines, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _h_0;
      return term_tsk(FID_doc_seen_lines, _t_3);
    }
    r0 = _h_0;
    WL_JMP(FID_doc_seen_lines);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check_k491)
    WL_POPN(1);
    Term _h_2 = STK(0);
    Term _h_1 = r0;
    WL_OPEN
    _h_2 = term_keep(e, _h_2, 1);
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _h_2;
      STK(1) = _h_1;
      STK(2) = FID_doc_seen_check_k492;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_doc_seen_check_k492, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _h_2;
      e.mem[_t_4 + 1] = _h_1;
      WL_CONT = term_tsk(FID_doc_seen_check_k492, _t_4);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_take)) {
      u64 _t_5 = task_node(e, FID_List_take, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _h_2;
      e.mem[_t_5 + 1] = 40ull;
      return term_tsk(FID_List_take, _t_5);
    }
    r0 = _h_2;
    r1 = 40ull;
    WL_JMP(FID_List_take);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check_k492)
    WL_POPN(2);
    Term _h_4 = STK(0);
    Term _h_5 = STK(1);
    Term _h_3 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _h_4;
      STK(1) = _h_5;
      STK(2) = FID_doc_seen_check_k493;
      WL_PUSHN(3);
    } else {
      u64 _t_6 = task_node(e, FID_doc_seen_check_k493, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _h_4;
      e.mem[_t_6 + 1] = _h_5;
      WL_CONT = term_tsk(FID_doc_seen_check_k493, _t_6);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_doc_seen_shows)) {
      u64 _t_7 = task_node(e, FID_doc_seen_shows, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _h_3;
      return term_tsk(FID_doc_seen_shows, _t_7);
    }
    r0 = _h_3;
    WL_JMP(FID_doc_seen_shows);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check_k493)
    WL_POPN(2);
    Term _h_7 = STK(0);
    Term _h_8 = STK(1);
    Term _h_6 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _h_7;
      STK(1) = _h_8;
      STK(2) = _h_6;
      STK(3) = FID_doc_seen_check_k494;
      WL_PUSHN(4);
    } else {
      u64 _t_8 = task_node(e, FID_doc_seen_check_k494, WL_CONT, WL_IDX, 1);
      e.mem[_t_8 + 0] = _h_7;
      e.mem[_t_8 + 1] = _h_8;
      e.mem[_t_8 + 2] = _h_6;
      WL_CONT = term_tsk(FID_doc_seen_check_k494, _t_8);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_List_length)) {
      u64 _t_9 = task_node(e, FID_List_length, WL_CONT, WL_IDX, 0);
      e.mem[_t_9 + 0] = _h_7;
      return term_tsk(FID_List_length, _t_9);
    }
    r0 = _h_7;
    WL_JMP(FID_List_length);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check_k494)
    WL_POPN(3);
    Term _h_10 = STK(0);
    Term _h_11 = STK(1);
    Term _h_12 = STK(2);
    Term _h_9 = r0;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_0[1];
    if (spin_32(e, _o_0, _h_9, 40ull) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_0[0];
    if (seq) {
      WL_ROOM(3, 0);
      STK(0) = _h_11;
      STK(1) = _h_12;
      STK(2) = FID_doc_seen_check_k495;
      WL_PUSHN(3);
    } else {
      u64 _t_10 = task_node(e, FID_doc_seen_check_k495, WL_CONT, WL_IDX, 1);
      e.mem[_t_10 + 0] = _h_11;
      e.mem[_t_10 + 1] = _h_12;
      WL_CONT = term_tsk(FID_doc_seen_check_k495, _t_10);
      WL_IDX = 2;
    }
    if (!DEVICE && !seq && fid_nofk(FID_doc_seen_whole_go)) {
      u64 _t_11 = task_node(e, FID_doc_seen_whole_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_11 + 0] = _v_0;
      e.mem[_t_11 + 1] = _h_10;
      return term_tsk(FID_doc_seen_whole_go, _t_11);
    }
    r0 = _v_0;
    r1 = _h_10;
    WL_JMP(FID_doc_seen_whole_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_seen_check_k495)
    WL_POPN(2);
    Term _h_14 = STK(0);
    Term _h_15 = STK(1);
    u32 _h_13 = r0;
    WL_OPEN
    r0 = _h_14;
    r1 = _h_15;
    r2 = _h_13;
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_prior)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_workflow_get_prior_k502;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_workflow_get_prior_k502, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_workflow_get_prior_k502, _t_0);
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
  WL_CASE(FID_ffi_workflow_get_prior_k502)
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
          STK(0) = FID_ffi_workflow_get_prior_k503;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_workflow_get_prior_k503, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_workflow_get_prior_k503, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_sts)) {
          u64 _t_3 = task_node(e, FID_ffi_workflow_get_sts, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_workflow_get_sts, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_workflow_get_sts);
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
  WL_CASE(FID_ffi_workflow_get_prior_k503)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_94(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_workflow_admit)
    u32 _prior_0 = r0;
    u32 _prior_1 = r1;
    Term _k_0 = r2;
    Term _rs_0 = r3;
    Term _p_0 = r4;
    Term _p_1 = r5;
    WL_OPEN
    if (_prior_0 == 1) {
      term_sink(e, _rs_0);
      u32 _v_0 = 0;
      Term _v_1 = 0;
      Term _o_0[2];
      if (spin_171(e, _o_0, _prior_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      _v_1 = _o_0[1];
      r0 = _v_0;
      r1 = _v_1;
      r2 = _p_0;
      r3 = _p_1;
      WL_RETN(4);
    } else {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _p_0;
        STK(1) = _p_1;
        STK(2) = FID_workflow_admit_k511;
        WL_PUSHN(3);
      } else {
        u64 _t_0 = task_node(e, FID_workflow_admit_k511, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _p_0;
        e.mem[_t_0 + 1] = _p_1;
        WL_CONT = term_tsk(FID_workflow_admit_k511, _t_0);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_workflow_found)) {
        u64 _t_1 = task_node(e, FID_workflow_found, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _rs_0;
        e.mem[_t_1 + 1] = _k_0;
        e.mem[_t_1 + 2] = 0;
        return term_tsk(FID_workflow_found, _t_1);
      }
      r0 = _rs_0;
      r1 = _k_0;
      r2 = 0;
      WL_JMP(FID_workflow_found);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_workflow_admit_k511)
    WL_POPN(2);
    Term _p_2 = STK(0);
    Term _p_3 = STK(1);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_3[4];
    if (spin_172(e, _o_3, _h_0, _h_1, _p_2, _p_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_3[0];
    r1 = _o_3[1];
    r2 = _o_3[2];
    r3 = _o_3[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_route)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_aux_fallback_get_route_k514;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_aux_fallback_get_route_k514, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_aux_fallback_get_route_k514, _t_0);
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
  WL_CASE(FID_ffi_aux_fallback_get_route_k514)
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
        r4 = 0;
        r5 = _h_2;
        WL_RETN(6);
      } else if (_h_1 == 1) {
        r0 = 0;
        r1 = 1;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = _h_2;
        WL_RETN(6);
      } else if (_h_1 == 2) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_route_k515;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_aux_fallback_get_route_k515, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_route_k515, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_key)) {
          u64 _t_3 = task_node(e, FID_ffi_aux_fallback_get_key, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_aux_fallback_get_key, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_aux_fallback_get_key);
      } else {
        Term _c_0 = (_h_1 - 3);
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
  WL_CASE(FID_ffi_aux_fallback_get_route_k515)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    WL_OPEN
    Term _o_0[6];
    if (spin_97(e, _o_0, _h_3, _h_4, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_gate)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_aux_fallback_get_gate_k519;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_aux_fallback_get_gate_k519, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_aux_fallback_get_gate_k519, _t_0);
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
  WL_CASE(FID_ffi_aux_fallback_get_gate_k519)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_gate_k520;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_aux_fallback_get_gate_k520, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_gate_k520, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_route)) {
          u64 _t_3 = task_node(e, FID_ffi_aux_fallback_get_route, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_aux_fallback_get_route, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_aux_fallback_get_route);
      } else if (_h_1 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_gate_k521;
          WL_PUSHN(1);
        } else {
          u64 _t_4 = task_node(e, FID_ffi_aux_fallback_get_gate_k521, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_gate_k521, _t_4);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_5);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else {
        Term _b_0 = (_h_1 - 2);
        term_sink(e, _h_2);
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
  WL_CASE(FID_ffi_aux_fallback_get_gate_k520)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    Term _h_8 = r5;
    WL_OPEN
    Term _o_0[7];
    if (spin_98(e, _o_0, _h_3, _h_4, _h_5, _h_6, _h_7, _h_8) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    r6 = _o_0[6];
    WL_RETN(7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_gate_k521)
    u32 _h_9 = r0;
    Term _h_10 = r1;
    Term _h_11 = r2;
    WL_OPEN
    if (_h_9 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_10;
        STK(1) = FID_ffi_aux_fallback_get_gate_k522;
        WL_PUSHN(2);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_aux_fallback_get_gate_k522, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _h_10;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_gate_k522, _t_6);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_7 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _h_11;
        return term_tsk(FID_wire_get_nat, _t_7);
      }
      r0 = _h_11;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_aux_fallback_get_gate_k522)
    WL_POPN(1);
    Term _h_15 = STK(0);
    u32 _h_12 = r0;
    Term _h_13 = r1;
    Term _h_14 = r2;
    WL_OPEN
    Term _o_1[7];
    if (spin_66(e, _o_1, _h_15, _h_12, _h_13, _h_14) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    r6 = _o_1[6];
    WL_RETN(7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_aux_fallback_after)
    u32 _r_0 = r0;
    Term _r_1 = r1;
    Term _r_2 = r2;
    Term _r_3 = r3;
    Term _sh_0 = r4;
    WL_OPEN
    if (_r_0 == 0) {
      r0 = _sh_0;
      WL_RETN(1);
    } else if (_r_0 == 1) {
      r0 = _sh_0;
      WL_RETN(1);
    } else {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _r_1;
        STK(1) = _r_2;
        STK(2) = _r_3;
        STK(3) = _sh_0;
        STK(4) = FID_aux_fallback_after_k529;
        WL_PUSHN(5);
      } else {
        u64 _t_0 = task_node(e, FID_aux_fallback_after_k529, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _r_1;
        e.mem[_t_0 + 1] = _r_2;
        e.mem[_t_0 + 2] = _r_3;
        e.mem[_t_0 + 3] = _sh_0;
        WL_CONT = term_tsk(FID_aux_fallback_after_k529, _t_0);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_aux_fallback_listed)) {
        u64 _t_1 = task_node(e, FID_aux_fallback_listed, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _sh_0;
        e.mem[_t_1 + 1] = _r_1;
        e.mem[_t_1 + 2] = _r_2;
        e.mem[_t_1 + 3] = _r_3;
        return term_tsk(FID_aux_fallback_listed, _t_1);
      }
      r0 = _sh_0;
      r1 = _r_1;
      r2 = _r_2;
      r3 = _r_3;
      WL_JMP(FID_aux_fallback_listed);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_aux_fallback_after_k529)
    WL_POPN(4);
    Term _r_4 = STK(0);
    Term _r_5 = STK(1);
    Term _r_6 = STK(2);
    Term _sh_1 = STK(3);
    u32 _h_0 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_177(e, _o_0, _h_0, _r_4, _r_5, _r_6, _sh_1) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_aux_fallback_put)
    u32 _r_0 = r0;
    Term _r_1 = r1;
    Term _r_2 = r2;
    Term _r_3 = r3;
    Term _sh_0 = r4;
    Term _t_0 = r5;
    WL_OPEN
    if (_r_0 == 0) {
      u64 _nd_0 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_0 + 0] = rfc_seal(e, term_pak(CID_aux_fallback_Stay, 0));
      e.mem[_nd_0 + 1] = rfc_seal(e, _t_0);
      r0 = term_ctr(CID_Con, _nd_0);
      WL_RETN(1);
    } else if (_r_0 == 1) {
      u64 _nd_1 = heap_alloc(e, cls_fit(2));
      e.mem[_nd_1 + 0] = rfc_seal(e, term_pak(CID_aux_fallback_Went, 0));
      e.mem[_nd_1 + 1] = rfc_seal(e, _t_0);
      r0 = term_ctr(CID_Con, _nd_1);
      WL_RETN(1);
    } else {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _r_1;
        STK(1) = _r_2;
        STK(2) = _r_3;
        STK(3) = _t_0;
        STK(4) = FID_aux_fallback_put_k531;
        WL_PUSHN(5);
      } else {
        u64 _t_1 = task_node(e, FID_aux_fallback_put_k531, WL_CONT, WL_IDX, 1);
        e.mem[_t_1 + 0] = _r_1;
        e.mem[_t_1 + 1] = _r_2;
        e.mem[_t_1 + 2] = _r_3;
        e.mem[_t_1 + 3] = _t_0;
        WL_CONT = term_tsk(FID_aux_fallback_put_k531, _t_1);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_aux_fallback_listed)) {
        u64 _t_2 = task_node(e, FID_aux_fallback_listed, WL_CONT, WL_IDX, 0);
        e.mem[_t_2 + 0] = _sh_0;
        e.mem[_t_2 + 1] = _r_1;
        e.mem[_t_2 + 2] = _r_2;
        e.mem[_t_2 + 3] = _r_3;
        return term_tsk(FID_aux_fallback_listed, _t_2);
      }
      r0 = _sh_0;
      r1 = _r_1;
      r2 = _r_2;
      r3 = _r_3;
      WL_JMP(FID_aux_fallback_listed);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_aux_fallback_put_k531)
    WL_POPN(4);
    Term _r_4 = STK(0);
    Term _r_5 = STK(1);
    Term _r_6 = STK(2);
    Term _t_3 = STK(3);
    u32 _h_0 = r0;
    WL_OPEN
    u64 _nd_2 = heap_alloc(e, cls_fit(3));
    e.mem[_nd_2 + 0] = rfc_seal(e, _r_4);
    e.mem[_nd_2 + 1] = rfc_seal(e, _r_5);
    e.mem[_nd_2 + 2] = rfc_seal(e, _r_6);
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_178(e, _o_0, _h_0, _r_4, _r_5, _r_6, _t_3) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    u64 _nd_5 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_5 + 0] = rfc_seal(e, term_ctr(CID_aux_fallback_Sub, _nd_2));
    e.mem[_nd_5 + 1] = rfc_seal(e, _v_0);
    r0 = term_ctr(CID_Con, _nd_5);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_str)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_str_k557;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_str_k557, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_str_k557, _t_0);
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
  WL_CASE(FID_wire_get_str_k557)
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
  WL_CASE(FID_ffi_doc_lines_get_mend)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_doc_lines_get_mend_k565;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_doc_lines_get_mend_k565, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_doc_lines_get_mend_k565, _t_0);
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
  WL_CASE(FID_ffi_doc_lines_get_mend_k565)
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
          STK(0) = FID_ffi_doc_lines_get_mend_k566;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_doc_lines_get_mend_k566, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_doc_lines_get_mend_k566, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_lines_get_end)) {
          u64 _t_3 = task_node(e, FID_ffi_doc_lines_get_end, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_doc_lines_get_end, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_doc_lines_get_end);
      } else {
        Term _p_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_doc_lines_get_mend_k566)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_151(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_doc_lines_plan)
    Term _rs_0 = r0;
    u32 _c_0 = r1;
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
      Term _fb_1[3];
      u64 _sp_1 = ctr_take(e, _f_0, 3, _fb_1);
      u32 _f_2 = _fb_1[0];
      u32 _f_3 = _fb_1[1];
      Term _f_4 = _fb_1[2];
      spare_free(e, cls_fit(3), _sp_1);
      if (_f_4 == 0) {
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _f_1;
        r1 = _c_0;
        _rs_0 = r0;
        _c_0 = r1;
        WL_AGAIN(FID_doc_lines_plan);
      } else {
        Term _m_0 = (_f_4 - 1);
        u32 _v_0 = 0;
        Term _o_0[1];
        if (spin_189(e, _o_0, _f_2, _f_3, _c_0) == 0) {
          return 0;
        }
        _v_0 = (u32)_o_0[0];
        spare_free(e, cls_fit(2), _sp_0);
        if (seq) {
          WL_ROOM(3, 0);
          STK(0) = _m_0;
          STK(1) = _v_0;
          STK(2) = FID_doc_lines_plan_k571;
          WL_PUSHN(3);
        } else {
          u64 _t_0 = task_node(e, FID_doc_lines_plan_k571, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _v_0;
          WL_CONT = term_tsk(FID_doc_lines_plan_k571, _t_0);
          WL_IDX = 2;
        }
        r0 = _f_1;
        r1 = _v_0;
        _rs_0 = r0;
        _c_0 = r1;
        WL_AGAIN(FID_doc_lines_plan);
      }
    }
    WL_SPUN
  }}
#endif

#if !DEVICE
  WL_CASE(FID_doc_lines_plan_k571)
    WL_POPN(2);
    Term _m_1 = STK(0);
    u32 _v_1 = STK(1);
    Term _h_0 = r0;
    WL_OPEN
    u64 _nd_0 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_0 + 0] = rfc_seal(e, _v_1);
    e.mem[_nd_0 + 1] = rfc_seal(e, nat_chk(e, _m_1 + 1));
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_doc_lines_Seps, _nd_0));
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_0);
    r0 = term_ctr(CID_Con, _nd_1);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_w)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_w_k585;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_w_k585, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_w_k585, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_maybe_nat)) {
      u64 _t_1 = task_node(e, FID_ffi_child_get_maybe_nat, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_ffi_child_get_maybe_nat, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_ffi_child_get_maybe_nat);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_w_k585)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_1;
        STK(1) = _h_2;
        STK(2) = FID_ffi_child_get_w_k586;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_child_get_w_k586, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        e.mem[_t_2 + 1] = _h_2;
        WL_CONT = term_tsk(FID_ffi_child_get_w_k586, _t_2);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_3;
        return term_tsk(FID_wire_get_nat, _t_3);
      }
      r0 = _h_3;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_child_get_w_k586)
    WL_POPN(2);
    u32 _h_7 = STK(0);
    Term _h_8 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    if (_h_4 == 0) {
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _h_7;
        STK(1) = _h_8;
        STK(2) = _h_5;
        STK(3) = FID_ffi_child_get_w_k587;
        WL_PUSHN(4);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_child_get_w_k587, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_7;
        e.mem[_t_4 + 1] = _h_8;
        e.mem[_t_4 + 2] = _h_5;
        WL_CONT = term_tsk(FID_ffi_child_get_w_k587, _t_4);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_6;
        return term_tsk(FID_wire_get_nat, _t_5);
      }
      r0 = _h_6;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_child_get_w_k587)
    WL_POPN(3);
    u32 _h_12 = STK(0);
    Term _h_13 = STK(1);
    Term _h_14 = STK(2);
    u32 _h_9 = r0;
    Term _h_10 = r1;
    Term _h_11 = r2;
    WL_OPEN
    Term _o_0[6];
    if (spin_113(e, _o_0, _h_12, _h_13, _h_14, _h_9, _h_10, _h_11) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    WL_RETN(6);
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
        STK(3) = FID_wire_cdig_go_k594;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_wire_cdig_go_k594, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        e.mem[_t_0 + 1] = _x_0;
        e.mem[_t_0 + 2] = _i_0;
        WL_CONT = term_tsk(FID_wire_cdig_go_k594, _t_0);
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
  WL_CASE(FID_wire_cdig_go_k594)
    WL_POPN(3);
    u32 _f_2 = STK(0);
    u32 _x_1 = STK(1);
    Term _i_1 = STK(2);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_0[2];
    if (spin_193(e, _o_0, U32_BIN(_x_1, ==, _f_2), _h_0, _h_1, _i_1) == 0) {
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
          STK(3) = FID_wire_get_nat_go_k597;
          WL_PUSHN(4);
        } else {
          u64 _t_1 = task_node(e, FID_wire_get_nat_go_k597, WL_CONT, WL_IDX, 1);
          e.mem[_t_1 + 0] = _j_0;
          e.mem[_t_1 + 1] = _ts_1;
          e.mem[_t_1 + 2] = _ds_0;
          WL_CONT = term_tsk(FID_wire_get_nat_go_k597, _t_1);
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
          STK(1) = FID_wire_get_nat_go_k598;
          WL_PUSHN(2);
        } else {
          u64 _t_4 = task_node(e, FID_wire_get_nat_go_k598, WL_CONT, WL_IDX, 1);
          e.mem[_t_4 + 0] = _ts_2;
          WL_CONT = term_tsk(FID_wire_get_nat_go_k598, _t_4);
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
  WL_CASE(FID_wire_get_nat_go_k597)
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
  WL_CASE(FID_wire_get_nat_go_k598)
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
        STK(1) = FID_wire_get_nat_end_k600;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_get_nat_end_k600, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _ts_2;
        WL_CONT = term_tsk(FID_wire_get_nat_end_k600, _t_0);
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
  WL_CASE(FID_wire_get_nat_end_k600)
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
  WL_CASE(FID_ffi_job_get_ev)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_job_get_ev_k610;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_job_get_ev_k610, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_job_get_ev_k610, _t_0);
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
  WL_CASE(FID_ffi_job_get_ev_k610)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_job_get_ev_k611;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_job_get_ev_k611, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_job_get_ev_k611, _t_2);
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
          STK(0) = FID_ffi_job_get_ev_k612;
          WL_PUSHN(1);
        } else {
          u64 _t_4 = task_node(e, FID_ffi_job_get_ev_k612, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_job_get_ev_k612, _t_4);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_job_get_code)) {
          u64 _t_5 = task_node(e, FID_ffi_job_get_code, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _h_2;
          return term_tsk(FID_ffi_job_get_code, _t_5);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_job_get_code);
      } else if (_h_1 == 2) {
        r0 = 0;
        r1 = 2;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else if (_h_1 == 3) {
        r0 = 0;
        r1 = 3;
        r2 = 0;
        r3 = 0;
        r4 = _h_2;
        WL_RETN(5);
      } else {
        Term _d_0 = (_h_1 - 4);
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
  WL_CASE(FID_ffi_job_get_ev_k611)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[5];
    if (spin_116(e, _o_0, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = (u32)_o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_job_get_ev_k612)
    u32 _h_6 = r0;
    u32 _h_7 = r1;
    u32 _h_8 = r2;
    Term _h_9 = r3;
    WL_OPEN
    Term _o_1[5];
    if (spin_117(e, _o_1, _h_6, _h_7, _h_8, _h_9) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = (u32)_o_1[3];
    r4 = _o_1[4];
    WL_RETN(5);
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
  WL_CASE(FID_ffi_admission_put_live)
    u32 _x_0 = r0;
    Term _x_1 = r1;
    Term _x_2 = r2;
    Term _x_3 = r3;
    Term _x_4 = r4;
    Term _rest_0 = r5;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_15(e, _o_0, _x_4, _rest_0) == 0) {
      return 0;
    }
    _v_0 = _o_0[0];
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _x_0;
      STK(1) = _x_1;
      STK(2) = _x_2;
      STK(3) = FID_ffi_admission_put_live_k627;
      WL_PUSHN(4);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_admission_put_live_k627, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _x_0;
      e.mem[_t_0 + 1] = _x_1;
      e.mem[_t_0 + 2] = _x_2;
      WL_CONT = term_tsk(FID_ffi_admission_put_live_k627, _t_0);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_0)) {
      u64 _t_1 = task_node(e, FID_wire_put_list_0, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _x_3;
      e.mem[_t_1 + 1] = _v_0;
      return term_tsk(FID_wire_put_list_0, _t_1);
    }
    r0 = _x_3;
    r1 = _v_0;
    WL_JMP(FID_wire_put_list_0);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_put_live_k627)
    WL_POPN(3);
    u32 _x_5 = STK(0);
    Term _x_6 = STK(1);
    Term _x_7 = STK(2);
    Term _h_0 = r0;
    WL_OPEN
    Term _v_1 = 0;
    Term _o_1[1];
    if (spin_15(e, _o_1, _x_7, _h_0) == 0) {
      return 0;
    }
    _v_1 = _o_1[0];
    Term _o_5[1];
    if (spin_199(e, _o_5, _x_5, _x_6, _v_1) == 0) {
      return 0;
    }
    r0 = _o_5[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step)
    u32 _x_0 = r0;
    Term _x_1 = r1;
    Term _x_2 = r2;
    Term _x_3 = r3;
    Term _x_4 = r4;
    u32 _o_0 = r5;
    Term _o_1 = r6;
    Term _o_2 = r7;
    Term _o_3 = r8;
    WL_OPEN
    if (_o_0 == 0) {
      if (_o_1 == 0) {
        if (seq) {
          WL_ROOM(5, 0);
          STK(0) = _x_0;
          STK(1) = _x_1;
          STK(2) = _x_2;
          STK(3) = _x_4;
          STK(4) = FID_admission_Live_step_k629;
          WL_PUSHN(5);
        } else {
          u64 _t_0 = task_node(e, FID_admission_Live_step_k629, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _x_0;
          e.mem[_t_0 + 1] = _x_1;
          e.mem[_t_0 + 2] = _x_2;
          e.mem[_t_0 + 3] = _x_4;
          WL_CONT = term_tsk(FID_admission_Live_step_k629, _t_0);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_admit_ia)) {
          u64 _t_1 = task_node(e, FID_admission_lv_admit_ia, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _x_0;
          e.mem[_t_1 + 1] = _x_1;
          e.mem[_t_1 + 2] = _x_2;
          e.mem[_t_1 + 3] = _x_3;
          e.mem[_t_1 + 4] = _x_4;
          return term_tsk(FID_admission_lv_admit_ia, _t_1);
        }
        r0 = _x_0;
        r1 = _x_1;
        r2 = _x_2;
        r3 = _x_3;
        r4 = _x_4;
        WL_JMP(FID_admission_lv_admit_ia);
      } else {
        if (seq) {
          WL_ROOM(5, 0);
          STK(0) = _x_0;
          STK(1) = _x_1;
          STK(2) = _x_2;
          STK(3) = _x_4;
          STK(4) = FID_admission_Live_step_k630;
          WL_PUSHN(5);
        } else {
          u64 _t_2 = task_node(e, FID_admission_Live_step_k630, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _x_0;
          e.mem[_t_2 + 1] = _x_1;
          e.mem[_t_2 + 2] = _x_2;
          e.mem[_t_2 + 3] = _x_4;
          WL_CONT = term_tsk(FID_admission_Live_step_k630, _t_2);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_lv_admit_bg)) {
          u64 _t_3 = task_node(e, FID_admission_lv_admit_bg, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _x_0;
          e.mem[_t_3 + 1] = _x_1;
          e.mem[_t_3 + 2] = _x_3;
          e.mem[_t_3 + 3] = _x_4;
          return term_tsk(FID_admission_lv_admit_bg, _t_3);
        }
        r0 = _x_0;
        r1 = _x_1;
        r2 = _x_3;
        r3 = _x_4;
        WL_JMP(FID_admission_lv_admit_bg);
      }
    } else if (_o_0 == 1) {
      if (seq) {
        WL_ROOM(7, 0);
        STK(0) = _x_0;
        STK(1) = _x_1;
        STK(2) = _x_2;
        STK(3) = _x_3;
        STK(4) = _x_4;
        STK(5) = _o_1;
        STK(6) = FID_admission_Live_step_k631;
        WL_PUSHN(7);
      } else {
        u64 _t_4 = task_node(e, FID_admission_Live_step_k631, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _x_0;
        e.mem[_t_4 + 1] = _x_1;
        e.mem[_t_4 + 2] = _x_2;
        e.mem[_t_4 + 3] = _x_3;
        e.mem[_t_4 + 4] = _x_4;
        e.mem[_t_4 + 5] = _o_1;
        WL_CONT = term_tsk(FID_admission_Live_step_k631, _t_4);
        WL_IDX = 6;
      }
      if (!DEVICE && !seq && fid_nofk(FID_admission_lv_find)) {
        u64 _t_5 = task_node(e, FID_admission_lv_find, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _x_3;
        e.mem[_t_5 + 1] = _o_1;
        return term_tsk(FID_admission_lv_find, _t_5);
      }
      r0 = _x_3;
      r1 = _o_1;
      WL_JMP(FID_admission_lv_find);
    } else if (_o_0 == 2) {
      if (seq) {
        WL_ROOM(7, 0);
        STK(0) = _x_0;
        STK(1) = _x_1;
        STK(2) = _x_2;
        STK(3) = _x_3;
        STK(4) = _x_4;
        STK(5) = _o_1;
        STK(6) = FID_admission_Live_step_k633;
        WL_PUSHN(7);
      } else {
        u64 _t_8 = task_node(e, FID_admission_Live_step_k633, WL_CONT, WL_IDX, 1);
        e.mem[_t_8 + 0] = _x_0;
        e.mem[_t_8 + 1] = _x_1;
        e.mem[_t_8 + 2] = _x_2;
        e.mem[_t_8 + 3] = _x_3;
        e.mem[_t_8 + 4] = _x_4;
        e.mem[_t_8 + 5] = _o_1;
        WL_CONT = term_tsk(FID_admission_Live_step_k633, _t_8);
        WL_IDX = 6;
      }
      if (!DEVICE && !seq && fid_nofk(FID_admission_lv_find)) {
        u64 _t_9 = task_node(e, FID_admission_lv_find, WL_CONT, WL_IDX, 0);
        e.mem[_t_9 + 0] = _x_3;
        e.mem[_t_9 + 1] = _o_1;
        return term_tsk(FID_admission_lv_find, _t_9);
      }
      r0 = _x_3;
      r1 = _o_1;
      WL_JMP(FID_admission_lv_find);
    } else if (_o_0 == 3) {
      if (seq) {
        WL_ROOM(7, 0);
        STK(0) = _x_0;
        STK(1) = _x_1;
        STK(2) = _x_2;
        STK(3) = _x_3;
        STK(4) = _x_4;
        STK(5) = _o_1;
        STK(6) = FID_admission_Live_step_k635;
        WL_PUSHN(7);
      } else {
        u64 _t_12 = task_node(e, FID_admission_Live_step_k635, WL_CONT, WL_IDX, 1);
        e.mem[_t_12 + 0] = _x_0;
        e.mem[_t_12 + 1] = _x_1;
        e.mem[_t_12 + 2] = _x_2;
        e.mem[_t_12 + 3] = _x_3;
        e.mem[_t_12 + 4] = _x_4;
        e.mem[_t_12 + 5] = _o_1;
        WL_CONT = term_tsk(FID_admission_Live_step_k635, _t_12);
        WL_IDX = 6;
      }
      if (!DEVICE && !seq && fid_nofk(FID_admission_lv_find)) {
        u64 _t_13 = task_node(e, FID_admission_lv_find, WL_CONT, WL_IDX, 0);
        e.mem[_t_13 + 0] = _x_3;
        e.mem[_t_13 + 1] = _o_1;
        return term_tsk(FID_admission_lv_find, _t_13);
      }
      r0 = _x_3;
      r1 = _o_1;
      WL_JMP(FID_admission_lv_find);
    } else {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _x_4;
        STK(1) = _o_1;
        STK(2) = _o_2;
        STK(3) = _o_3;
        STK(4) = FID_admission_Live_step_k637;
        WL_PUSHN(5);
      } else {
        u64 _t_16 = task_node(e, FID_admission_Live_step_k637, WL_CONT, WL_IDX, 1);
        e.mem[_t_16 + 0] = _x_4;
        e.mem[_t_16 + 1] = _o_1;
        e.mem[_t_16 + 2] = _o_2;
        e.mem[_t_16 + 3] = _o_3;
        WL_CONT = term_tsk(FID_admission_Live_step_k637, _t_16);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_admission_lv_grant)) {
        u64 _t_17 = task_node(e, FID_admission_lv_grant, WL_CONT, WL_IDX, 0);
        e.mem[_t_17 + 0] = _o_1;
        e.mem[_t_17 + 1] = _o_2;
        e.mem[_t_17 + 2] = _x_3;
        return term_tsk(FID_admission_lv_grant, _t_17);
      }
      r0 = _o_1;
      r1 = _o_2;
      r2 = _x_3;
      WL_JMP(FID_admission_lv_grant);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k629)
    WL_POPN(4);
    u32 _x_5 = STK(0);
    Term _x_6 = STK(1);
    Term _x_7 = STK(2);
    Term _x_8 = STK(3);
    Term _h_0 = r0;
    WL_OPEN
    r0 = _x_5;
    r1 = _x_6;
    r2 = _x_7;
    r3 = _h_0;
    r4 = nat_chk(e, _x_8 + 1);
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k630)
    WL_POPN(4);
    u32 _x_9 = STK(0);
    Term _x_10 = STK(1);
    Term _x_11 = STK(2);
    Term _x_12 = STK(3);
    Term _h_1 = r0;
    WL_OPEN
    r0 = _x_9;
    r1 = _x_10;
    r2 = _x_11;
    r3 = _h_1;
    r4 = nat_chk(e, _x_12 + 1);
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k631)
    WL_POPN(6);
    u32 _x_13 = STK(0);
    Term _x_14 = STK(1);
    Term _x_15 = STK(2);
    Term _x_16 = STK(3);
    Term _x_17 = STK(4);
    Term _o_4 = STK(5);
    u32 _h_2 = r0;
    u32 _h_3 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _x_13;
      STK(1) = _x_14;
      STK(2) = _x_15;
      STK(3) = _x_17;
      STK(4) = FID_admission_Live_step_k632;
      WL_PUSHN(5);
    } else {
      u64 _t_6 = task_node(e, FID_admission_Live_step_k632, WL_CONT, WL_IDX, 1);
      e.mem[_t_6 + 0] = _x_13;
      e.mem[_t_6 + 1] = _x_14;
      e.mem[_t_6 + 2] = _x_15;
      e.mem[_t_6 + 3] = _x_17;
      WL_CONT = term_tsk(FID_admission_Live_step_k632, _t_6);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_collect)) {
      u64 _t_7 = task_node(e, FID_admission_lv_collect, WL_CONT, WL_IDX, 0);
      e.mem[_t_7 + 0] = _h_2;
      e.mem[_t_7 + 1] = _h_3;
      e.mem[_t_7 + 2] = _x_16;
      e.mem[_t_7 + 3] = _o_4;
      return term_tsk(FID_admission_lv_collect, _t_7);
    }
    r0 = _h_2;
    r1 = _h_3;
    r2 = _x_16;
    r3 = _o_4;
    WL_JMP(FID_admission_lv_collect);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k632)
    WL_POPN(4);
    u32 _x_18 = STK(0);
    Term _x_19 = STK(1);
    Term _x_20 = STK(2);
    Term _x_21 = STK(3);
    Term _h_4 = r0;
    WL_OPEN
    r0 = _x_18;
    r1 = _x_19;
    r2 = _x_20;
    r3 = _h_4;
    r4 = _x_21;
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k633)
    WL_POPN(6);
    u32 _x_22 = STK(0);
    Term _x_23 = STK(1);
    Term _x_24 = STK(2);
    Term _x_25 = STK(3);
    Term _x_26 = STK(4);
    Term _o_5 = STK(5);
    u32 _h_5 = r0;
    u32 _h_6 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _x_22;
      STK(1) = _x_23;
      STK(2) = _x_24;
      STK(3) = _x_26;
      STK(4) = FID_admission_Live_step_k634;
      WL_PUSHN(5);
    } else {
      u64 _t_10 = task_node(e, FID_admission_Live_step_k634, WL_CONT, WL_IDX, 1);
      e.mem[_t_10 + 0] = _x_22;
      e.mem[_t_10 + 1] = _x_23;
      e.mem[_t_10 + 2] = _x_24;
      e.mem[_t_10 + 3] = _x_26;
      WL_CONT = term_tsk(FID_admission_Live_step_k634, _t_10);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_release)) {
      u64 _t_11 = task_node(e, FID_admission_lv_release, WL_CONT, WL_IDX, 0);
      e.mem[_t_11 + 0] = _h_5;
      e.mem[_t_11 + 1] = _h_6;
      e.mem[_t_11 + 2] = _x_22;
      e.mem[_t_11 + 3] = _x_23;
      e.mem[_t_11 + 4] = _x_25;
      e.mem[_t_11 + 5] = _o_5;
      return term_tsk(FID_admission_lv_release, _t_11);
    }
    r0 = _h_5;
    r1 = _h_6;
    r2 = _x_22;
    r3 = _x_23;
    r4 = _x_25;
    r5 = _o_5;
    WL_JMP(FID_admission_lv_release);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k634)
    WL_POPN(4);
    u32 _x_27 = STK(0);
    Term _x_28 = STK(1);
    Term _x_29 = STK(2);
    Term _x_30 = STK(3);
    Term _h_7 = r0;
    WL_OPEN
    r0 = _x_27;
    r1 = _x_28;
    r2 = _x_29;
    r3 = _h_7;
    r4 = _x_30;
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k635)
    WL_POPN(6);
    u32 _x_31 = STK(0);
    Term _x_32 = STK(1);
    Term _x_33 = STK(2);
    Term _x_34 = STK(3);
    Term _x_35 = STK(4);
    Term _o_6 = STK(5);
    u32 _h_8 = r0;
    u32 _h_9 = r1;
    WL_OPEN
    if (seq) {
      WL_ROOM(5, 0);
      STK(0) = _x_31;
      STK(1) = _x_32;
      STK(2) = _x_33;
      STK(3) = _x_35;
      STK(4) = FID_admission_Live_step_k636;
      WL_PUSHN(5);
    } else {
      u64 _t_14 = task_node(e, FID_admission_Live_step_k636, WL_CONT, WL_IDX, 1);
      e.mem[_t_14 + 0] = _x_31;
      e.mem[_t_14 + 1] = _x_32;
      e.mem[_t_14 + 2] = _x_33;
      e.mem[_t_14 + 3] = _x_35;
      WL_CONT = term_tsk(FID_admission_Live_step_k636, _t_14);
      WL_IDX = 4;
    }
    if (!DEVICE && !seq && fid_nofk(FID_admission_lv_leave)) {
      u64 _t_15 = task_node(e, FID_admission_lv_leave, WL_CONT, WL_IDX, 0);
      e.mem[_t_15 + 0] = _h_8;
      e.mem[_t_15 + 1] = _h_9;
      e.mem[_t_15 + 2] = _x_31;
      e.mem[_t_15 + 3] = _x_32;
      e.mem[_t_15 + 4] = _x_34;
      e.mem[_t_15 + 5] = _o_6;
      return term_tsk(FID_admission_lv_leave, _t_15);
    }
    r0 = _h_8;
    r1 = _h_9;
    r2 = _x_31;
    r3 = _x_32;
    r4 = _x_34;
    r5 = _o_6;
    WL_JMP(FID_admission_lv_leave);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k636)
    WL_POPN(4);
    u32 _x_36 = STK(0);
    Term _x_37 = STK(1);
    Term _x_38 = STK(2);
    Term _x_39 = STK(3);
    Term _h_10 = r0;
    WL_OPEN
    r0 = _x_36;
    r1 = _x_37;
    r2 = _x_38;
    r3 = _h_10;
    r4 = _x_39;
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_admission_Live_step_k637)
    WL_POPN(4);
    Term _x_40 = STK(0);
    u32 _o_7 = STK(1);
    Term _o_8 = STK(2);
    Term _o_9 = STK(3);
    Term _h_11 = r0;
    WL_OPEN
    r0 = _o_7;
    r1 = _o_8;
    r2 = _o_9;
    r3 = _h_11;
    r4 = _x_40;
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_doc_seen_get_iv)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_doc_seen_get_iv_k640;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_doc_seen_get_iv_k640, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_doc_seen_get_iv_k640, _t_0);
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
  WL_CASE(FID_ffi_doc_seen_get_iv_k640)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_doc_seen_get_iv_k641;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_doc_seen_get_iv_k641, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_doc_seen_get_iv_k641, _t_2);
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
  WL_CASE(FID_ffi_doc_seen_get_iv_k641)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_168(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
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
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_doc_seen_Iv, _nd_0));
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
          STK(3) = FID_wire_get_list_go_5_k643;
          WL_PUSHN(4);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_5_k643, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          WL_CONT = term_tsk(FID_wire_get_list_go_5_k643, _t_0);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_seen_get_iv)) {
          u64 _t_1 = task_node(e, FID_ffi_doc_seen_get_iv, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_3;
          return term_tsk(FID_ffi_doc_seen_get_iv, _t_1);
        }
        r0 = _cur_3;
        WL_JMP(FID_ffi_doc_seen_get_iv);
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
  WL_CASE(FID_wire_get_list_go_5_k643)
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
      STK(2) = FID_wire_get_list_go_5_k644;
      WL_PUSHN(3);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_5_k644, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_4;
      e.mem[_t_2 + 1] = _cur_5;
      WL_CONT = term_tsk(FID_wire_get_list_go_5_k644, _t_2);
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
  WL_CASE(FID_wire_get_list_go_5_k644)
    WL_POPN(2);
    Term _cur_6 = STK(0);
    Term _cur_7 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_201(e, _o_0, _cur_6, _cur_7, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_progress_get_prior)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_progress_get_prior_k680;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_progress_get_prior_k680, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_progress_get_prior_k680, _t_0);
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
  WL_CASE(FID_ffi_progress_get_prior_k680)
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
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_progress_get_prior_k681;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_progress_get_prior_k681, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_progress_get_prior_k681, _t_2);
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
        Term _q_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_progress_get_prior_k681)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_4;
        STK(1) = FID_ffi_progress_get_prior_k682;
        WL_PUSHN(2);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_progress_get_prior_k682, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_4;
        WL_CONT = term_tsk(FID_ffi_progress_get_prior_k682, _t_4);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_wire_get_nat, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_progress_get_prior_k682)
    WL_POPN(1);
    Term _h_9 = STK(0);
    u32 _h_6 = r0;
    Term _h_7 = r1;
    Term _h_8 = r2;
    WL_OPEN
    Term _o_0[5];
    if (spin_103(e, _o_0, _h_9, _h_6, _h_7, _h_8) == 0) {
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
  WL_CASE(FID_ffi_doc_lines_get_run)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_doc_lines_get_run_k696;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_doc_lines_get_run_k696, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_doc_lines_get_run_k696, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_lines_get_mend)) {
      u64 _t_1 = task_node(e, FID_ffi_doc_lines_get_mend, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_ffi_doc_lines_get_mend, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_ffi_doc_lines_get_mend);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_doc_lines_get_run_k696)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    u32 _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_1;
        STK(1) = _h_2;
        STK(2) = FID_ffi_doc_lines_get_run_k697;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_doc_lines_get_run_k697, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        e.mem[_t_2 + 1] = _h_2;
        WL_CONT = term_tsk(FID_ffi_doc_lines_get_run_k697, _t_2);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_3;
        return term_tsk(FID_wire_get_nat, _t_3);
      }
      r0 = _h_3;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_doc_lines_get_run_k697)
    WL_POPN(2);
    u32 _h_7 = STK(0);
    u32 _h_8 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[5];
    if (spin_188(e, _o_0, _h_7, _h_8, _h_4, _h_5, _h_6) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = (u32)_o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    WL_RETN(5);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_3)
    Term _n_0 = r0;
    u32 _cur_0 = r1;
    u32 _cur_1 = r2;
    u32 _cur_2 = r3;
    Term _cur_3 = r4;
    Term _cur_4 = r5;
    WL_OPEN
    if (_n_0 == 0) {
      if (_cur_0 == 0) {
        u64 _nd_0 = heap_alloc(e, cls_fit(3));
        e.mem[_nd_0 + 0] = rfc_seal(e, _cur_1);
        e.mem[_nd_0 + 1] = rfc_seal(e, _cur_2);
        e.mem[_nd_0 + 2] = rfc_seal(e, _cur_3);
        u64 _nd_1 = heap_alloc(e, cls_fit(2));
        e.mem[_nd_1 + 0] = rfc_seal(e, term_ctr(CID_doc_lines_Run, _nd_0));
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
          STK(4) = FID_wire_get_list_go_3_k699;
          WL_PUSHN(5);
        } else {
          u64 _t_0 = task_node(e, FID_wire_get_list_go_3_k699, WL_CONT, WL_IDX, 1);
          e.mem[_t_0 + 0] = _m_0;
          e.mem[_t_0 + 1] = _cur_1;
          e.mem[_t_0 + 2] = _cur_2;
          e.mem[_t_0 + 3] = _cur_3;
          WL_CONT = term_tsk(FID_wire_get_list_go_3_k699, _t_0);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_lines_get_run)) {
          u64 _t_1 = task_node(e, FID_ffi_doc_lines_get_run, WL_CONT, WL_IDX, 0);
          e.mem[_t_1 + 0] = _cur_4;
          return term_tsk(FID_ffi_doc_lines_get_run, _t_1);
        }
        r0 = _cur_4;
        WL_JMP(FID_ffi_doc_lines_get_run);
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
  WL_CASE(FID_wire_get_list_go_3_k699)
    WL_POPN(4);
    Term _m_1 = STK(0);
    u32 _cur_5 = STK(1);
    u32 _cur_6 = STK(2);
    Term _cur_7 = STK(3);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    u32 _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _cur_5;
      STK(1) = _cur_6;
      STK(2) = _cur_7;
      STK(3) = FID_wire_get_list_go_3_k700;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_wire_get_list_go_3_k700, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _cur_5;
      e.mem[_t_2 + 1] = _cur_6;
      e.mem[_t_2 + 2] = _cur_7;
      WL_CONT = term_tsk(FID_wire_get_list_go_3_k700, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_3)) {
      u64 _t_3 = task_node(e, FID_wire_get_list_go_3, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = _m_1;
      e.mem[_t_3 + 1] = _h_0;
      e.mem[_t_3 + 2] = _h_1;
      e.mem[_t_3 + 3] = _h_2;
      e.mem[_t_3 + 4] = _h_3;
      e.mem[_t_3 + 5] = _h_4;
      return term_tsk(FID_wire_get_list_go_3, _t_3);
    }
    r0 = _m_1;
    r1 = _h_0;
    r2 = _h_1;
    r3 = _h_2;
    r4 = _h_3;
    r5 = _h_4;
    WL_JMP(FID_wire_get_list_go_3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_list_go_3_k700)
    WL_POPN(3);
    u32 _cur_8 = STK(0);
    u32 _cur_9 = STK(1);
    Term _cur_10 = STK(2);
    u32 _h_5 = r0;
    Term _h_6 = r1;
    Term _h_7 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_216(e, _o_0, _cur_8, _cur_9, _cur_10, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = _o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_ph)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_ph_k706;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_ph_k706, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_ph_k706, _t_0);
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
  WL_CASE(FID_ffi_child_get_ph_k706)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _h_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      if (_v_0 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_child_get_ph_k707;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_child_get_ph_k707, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_child_get_ph_k707, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_w)) {
          u64 _t_3 = task_node(e, FID_ffi_child_get_w, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_child_get_w, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_child_get_w);
      } else if (_v_0 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_child_get_ph_k708;
          WL_PUSHN(1);
        } else {
          u64 _t_4 = task_node(e, FID_ffi_child_get_ph_k708, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_child_get_ph_k708, _t_4);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_report)) {
          u64 _t_5 = task_node(e, FID_ffi_child_get_report, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _h_2;
          return term_tsk(FID_ffi_child_get_report, _t_5);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_child_get_report);
      } else if (_v_0 == 2) {
        r0 = 0;
        r1 = 2;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = _h_2;
        WL_RETN(7);
      } else if (_v_0 == 3) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = 0;
        WL_RETN(7);
      } else if (_v_0 == 4) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = 0;
        WL_RETN(7);
      } else {
        term_sink(e, _h_2);
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
  WL_CASE(FID_ffi_child_get_ph_k707)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    Term _h_8 = r5;
    WL_OPEN
    Term _o_1[7];
    if (spin_153(e, _o_1, _h_3, _h_4, _h_5, _h_6, _h_7, _h_8) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = (u32)_o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    r6 = _o_1[6];
    WL_RETN(7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_ph_k708)
    u32 _h_9 = r0;
    u32 _h_10 = r1;
    Term _h_11 = r2;
    WL_OPEN
    if (_h_9 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_10;
        STK(1) = FID_ffi_child_get_ph_k709;
        WL_PUSHN(2);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_child_get_ph_k709, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _h_10;
        WL_CONT = term_tsk(FID_ffi_child_get_ph_k709, _t_6);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_7 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _h_11;
        return term_tsk(FID_wire_get_nat, _t_7);
      }
      r0 = _h_11;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_child_get_ph_k709)
    WL_POPN(1);
    u32 _h_15 = STK(0);
    u32 _h_12 = r0;
    Term _h_13 = r1;
    Term _h_14 = r2;
    WL_OPEN
    Term _o_2[7];
    if (spin_110(e, _o_2, _h_15, _h_12, _h_13, _h_14) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = (u32)_o_2[2];
    r3 = _o_2[3];
    r4 = _o_2[4];
    r5 = _o_2[5];
    r6 = _o_2[6];
    WL_RETN(7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_mfate)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_mfate_k712;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_mfate_k712, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_mfate_k712, _t_0);
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
  WL_CASE(FID_ffi_child_get_mfate_k712)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_47(e, _o_0, _h_1) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      if (_v_0 == 0) {
        r0 = 0;
        r1 = 0;
        r2 = 0;
        r3 = _h_2;
        WL_RETN(4);
      } else if (_v_0 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_child_get_mfate_k713;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_child_get_mfate_k713, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_child_get_mfate_k713, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_fate)) {
          u64 _t_3 = task_node(e, FID_ffi_child_get_fate, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_child_get_fate, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_child_get_fate);
      } else if (_v_0 == 2) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      } else if (_v_0 == 3) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      } else if (_v_0 == 4) {
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        WL_RETN(4);
      } else {
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
  WL_CASE(FID_ffi_child_get_mfate_k713)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_1[4];
    if (spin_156(e, _o_1, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = (u32)_o_1[2];
    r3 = _o_1[3];
    WL_RETN(4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_child_get_cfg)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_child_get_cfg_k717;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_child_get_cfg_k717, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_child_get_cfg_k717, _t_0);
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
  WL_CASE(FID_ffi_child_get_cfg_k717)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_child_get_cfg_k718;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_child_get_cfg_k718, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_child_get_cfg_k718, _t_2);
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
  WL_CASE(FID_ffi_child_get_cfg_k718)
    WL_POPN(1);
    Term _h_6 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_192(e, _o_0, _h_6, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_wire_tok)
    u32 _c_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _c_0;
      STK(1) = FID_wire_tok_k725;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_wire_tok_k725, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _c_0;
      WL_CONT = term_tsk(FID_wire_tok_k725, _t_0);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_cdig_go)) {
      u64 _t_1 = task_node(e, FID_wire_cdig_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = term_ctr(CID_Con, STAT_OFF + 382);
      e.mem[_t_1 + 1] = _c_0;
      e.mem[_t_1 + 2] = 0;
      return term_tsk(FID_wire_cdig_go, _t_1);
    }
    r0 = term_ctr(CID_Con, STAT_OFF + 382);
    r1 = _c_0;
    r2 = 0;
    WL_JMP(FID_wire_cdig_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_tok_k725)
    WL_POPN(1);
    u32 _c_1 = STK(0);
    u32 _h_0 = r0;
    Term _h_1 = r1;
    WL_OPEN
    Term _o_1[2];
    if (spin_219(e, _o_1, _h_0, _h_1, U32_BIN(_c_1, ==, 44ull)) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = _o_1[1];
    WL_RETN(2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_job_get_job)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_job_get_job_k730;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_job_get_job_k730, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_job_get_job_k730, _t_0);
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
  WL_CASE(FID_ffi_job_get_job_k730)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_job_get_job_k731;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_job_get_job_k731, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_job_get_job_k731, _t_2);
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
          STK(0) = FID_ffi_job_get_job_k733;
          WL_PUSHN(1);
        } else {
          u64 _t_6 = task_node(e, FID_ffi_job_get_job_k733, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_job_get_job_k733, _t_6);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_7 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_7 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_7);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else {
        Term _q_0 = (_h_1 - 2);
        term_sink(e, _h_2);
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
  WL_CASE(FID_ffi_job_get_job_k731)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_4;
        STK(1) = FID_ffi_job_get_job_k732;
        WL_PUSHN(2);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_job_get_job_k732, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_4;
        WL_CONT = term_tsk(FID_ffi_job_get_job_k732, _t_4);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_wire_get_nat, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_job_get_job_k732)
    WL_POPN(1);
    Term _h_9 = STK(0);
    u32 _h_6 = r0;
    Term _h_7 = r1;
    Term _h_8 = r2;
    WL_OPEN
    Term _o_0[8];
    if (spin_115(e, _o_0, _h_9, _h_6, _h_7, _h_8) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = (u32)_o_0[4];
    r5 = (u32)_o_0[5];
    r6 = (u32)_o_0[6];
    r7 = _o_0[7];
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_job_get_job_k733)
    u32 _h_10 = r0;
    Term _h_11 = r1;
    Term _h_12 = r2;
    WL_OPEN
    if (_h_10 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_11;
        STK(1) = FID_ffi_job_get_job_k734;
        WL_PUSHN(2);
      } else {
        u64 _t_8 = task_node(e, FID_ffi_job_get_job_k734, WL_CONT, WL_IDX, 1);
        e.mem[_t_8 + 0] = _h_11;
        WL_CONT = term_tsk(FID_ffi_job_get_job_k734, _t_8);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_9 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_9 + 0] = _h_12;
        return term_tsk(FID_wire_get_nat, _t_9);
      }
      r0 = _h_12;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_job_get_job_k734)
    WL_POPN(1);
    Term _h_16 = STK(0);
    u32 _h_13 = r0;
    Term _h_14 = r1;
    Term _h_15 = r2;
    WL_OPEN
    if (_h_13 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_16;
        STK(1) = _h_14;
        STK(2) = FID_ffi_job_get_job_k735;
        WL_PUSHN(3);
      } else {
        u64 _t_10 = task_node(e, FID_ffi_job_get_job_k735, WL_CONT, WL_IDX, 1);
        e.mem[_t_10 + 0] = _h_16;
        e.mem[_t_10 + 1] = _h_14;
        WL_CONT = term_tsk(FID_ffi_job_get_job_k735, _t_10);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_job_get_end)) {
        u64 _t_11 = task_node(e, FID_ffi_job_get_end, WL_CONT, WL_IDX, 0);
        e.mem[_t_11 + 0] = _h_15;
        return term_tsk(FID_ffi_job_get_end, _t_11);
      }
      r0 = _h_15;
      WL_JMP(FID_ffi_job_get_end);
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
  WL_CASE(FID_ffi_job_get_job_k735)
    WL_POPN(2);
    Term _h_22 = STK(0);
    Term _h_23 = STK(1);
    u32 _h_17 = r0;
    u32 _h_18 = r1;
    u32 _h_19 = r2;
    u32 _h_20 = r3;
    Term _h_21 = r4;
    WL_OPEN
    Term _o_1[8];
    if (spin_80(e, _o_1, _h_22, _h_23, _h_17, _h_18, _h_19, _h_20, _h_21) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = (u32)_o_1[4];
    r5 = (u32)_o_1[5];
    r6 = (u32)_o_1[6];
    r7 = _o_1[7];
    WL_RETN(8);
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
        if (spin_200(e, _o_0, _a_1, _a_2) == 0) {
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
  WL_CASE(FID_wire_get_list_4)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_4_k761;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_4_k761, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_4_k761, _t_0);
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
  WL_CASE(FID_wire_get_list_4_k761)
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
          STK(1) = FID_wire_get_list_4_k762;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_4_k762, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_4_k762, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_seen_get_at)) {
          u64 _t_3 = task_node(e, FID_ffi_doc_seen_get_at, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_doc_seen_get_at, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_doc_seen_get_at);
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
  WL_CASE(FID_wire_get_list_4_k762)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    Term _h_4 = r1;
    u32 _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_4)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_4, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      e.mem[_t_4 + 5] = _h_7;
      return term_tsk(FID_wire_get_list_go_4, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    WL_JMP(FID_wire_get_list_go_4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_default_model_get_saved)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_default_model_get_saved_k790;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_default_model_get_saved_k790, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_default_model_get_saved_k790, _t_0);
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
  WL_CASE(FID_ffi_default_model_get_saved_k790)
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
          STK(0) = FID_ffi_default_model_get_saved_k791;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_default_model_get_saved_k791, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_default_model_get_saved_k791, _t_2);
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
        Term _b_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_default_model_get_saved_k791)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_181(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_wire_get_u32)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_u32_k800;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_u32_k800, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_u32_k800, _t_0);
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
  WL_CASE(FID_wire_get_u32_k800)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_2[3];
    if (spin_223(e, _o_2, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    WL_RETN(3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_doc_lines_get_end)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_doc_lines_get_end_k813;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_doc_lines_get_end_k813, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_doc_lines_get_end_k813, _t_0);
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
  WL_CASE(FID_ffi_doc_lines_get_end_k813)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    Term _o_0[3];
    if (spin_225(e, _o_0, _h_0, _h_1, _h_2) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    WL_RETN(3);
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
        STK(1) = FID_wire_peek_k828;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_wire_peek_k828, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_1;
        WL_CONT = term_tsk(FID_wire_peek_k828, _t_0);
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
  WL_CASE(FID_wire_peek_k828)
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
  WL_CASE(FID_ffi_job_get_cap)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_job_get_cap_k832;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_job_get_cap_k832, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_job_get_cap_k832, _t_0);
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
  WL_CASE(FID_ffi_job_get_cap_k832)
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
          STK(0) = FID_ffi_job_get_cap_k833;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_job_get_cap_k833, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_job_get_cap_k833, _t_2);
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
        Term _q_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_job_get_cap_k833)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_195(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_ffi_admission_get_lim)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_admission_get_lim_k839;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_admission_get_lim_k839, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_admission_get_lim_k839, _t_0);
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
  WL_CASE(FID_ffi_admission_get_lim_k839)
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
          STK(0) = FID_ffi_admission_get_lim_k840;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_admission_get_lim_k840, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_get_lim_k840, _t_2);
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
  WL_CASE(FID_ffi_admission_get_lim_k840)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_196(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_U32_show)
    u32 _a_0 = r0;
    WL_OPEN
    u32 _s_0 = U32_BIN(_a_0, ==, 0);
    if (_s_0 == 1) {
      r0 = term_ctr(CID_SCon, STAT_OFF + 674);
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
  WL_CASE(FID_ffi_admission_get_op)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_admission_get_op_k848;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_admission_get_op_k848, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_admission_get_op_k848, _t_0);
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
  WL_CASE(FID_ffi_admission_get_op_k848)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_admission_get_op_k849;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_admission_get_op_k849, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_get_op_k849, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_get_cls)) {
          u64 _t_3 = task_node(e, FID_ffi_admission_get_cls, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_admission_get_cls, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_admission_get_cls);
      } else if (_h_1 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_admission_get_op_k850;
          WL_PUSHN(1);
        } else {
          u64 _t_4 = task_node(e, FID_ffi_admission_get_op_k850, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_get_op_k850, _t_4);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_5 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_5);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 2) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_admission_get_op_k851;
          WL_PUSHN(1);
        } else {
          u64 _t_6 = task_node(e, FID_ffi_admission_get_op_k851, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_get_op_k851, _t_6);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_7 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_7 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_7);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 3) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_admission_get_op_k852;
          WL_PUSHN(1);
        } else {
          u64 _t_8 = task_node(e, FID_ffi_admission_get_op_k852, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_get_op_k852, _t_8);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
          u64 _t_9 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
          e.mem[_t_9 + 0] = _h_2;
          return term_tsk(FID_wire_get_nat, _t_9);
        }
        r0 = _h_2;
        WL_JMP(FID_wire_get_nat);
      } else if (_h_1 == 4) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_admission_get_op_k853;
          WL_PUSHN(1);
        } else {
          u64 _t_10 = task_node(e, FID_ffi_admission_get_op_k853, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_get_op_k853, _t_10);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_get_lim)) {
          u64 _t_11 = task_node(e, FID_ffi_admission_get_lim, WL_CONT, WL_IDX, 0);
          e.mem[_t_11 + 0] = _h_2;
          return term_tsk(FID_ffi_admission_get_lim, _t_11);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_admission_get_lim);
      } else {
        Term _e_0 = (_h_1 - 5);
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
  WL_CASE(FID_ffi_admission_get_op_k849)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[6];
    if (spin_197(e, _o_0, _h_3, _h_4, _h_5) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_get_op_k850)
    u32 _h_6 = r0;
    Term _h_7 = r1;
    Term _h_8 = r2;
    WL_OPEN
    Term _o_1[6];
    if (spin_198(e, _o_1, _h_6, _h_7, _h_8, 0) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_get_op_k851)
    u32 _h_9 = r0;
    Term _h_10 = r1;
    Term _h_11 = r2;
    WL_OPEN
    Term _o_2[6];
    if (spin_198(e, _o_2, _h_9, _h_10, _h_11, 1ull) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    r3 = _o_2[3];
    r4 = _o_2[4];
    r5 = _o_2[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_get_op_k852)
    u32 _h_12 = r0;
    Term _h_13 = r1;
    Term _h_14 = r2;
    WL_OPEN
    Term _o_3[6];
    if (spin_198(e, _o_3, _h_12, _h_13, _h_14, 2ull) == 0) {
      return 0;
    }
    r0 = (u32)_o_3[0];
    r1 = (u32)_o_3[1];
    r2 = _o_3[2];
    r3 = _o_3[3];
    r4 = _o_3[4];
    r5 = _o_3[5];
    WL_RETN(6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_get_op_k853)
    u32 _h_15 = r0;
    u32 _h_16 = r1;
    Term _h_17 = r2;
    Term _h_18 = r3;
    WL_OPEN
    if (_h_15 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_16;
        STK(1) = _h_17;
        STK(2) = FID_ffi_admission_get_op_k854;
        WL_PUSHN(3);
      } else {
        u64 _t_12 = task_node(e, FID_ffi_admission_get_op_k854, WL_CONT, WL_IDX, 1);
        e.mem[_t_12 + 0] = _h_16;
        e.mem[_t_12 + 1] = _h_17;
        WL_CONT = term_tsk(FID_ffi_admission_get_op_k854, _t_12);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_13 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_13 + 0] = _h_18;
        return term_tsk(FID_wire_get_nat, _t_13);
      }
      r0 = _h_18;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_admission_get_op_k854)
    WL_POPN(2);
    u32 _h_22 = STK(0);
    Term _h_23 = STK(1);
    u32 _h_19 = r0;
    Term _h_20 = r1;
    Term _h_21 = r2;
    WL_OPEN
    Term _o_4[6];
    if (spin_161(e, _o_4, _h_22, _h_23, _h_19, _h_20, _h_21) == 0) {
      return 0;
    }
    r0 = (u32)_o_4[0];
    r1 = (u32)_o_4[1];
    r2 = _o_4[2];
    r3 = _o_4[3];
    r4 = _o_4[4];
    r5 = _o_4[5];
    WL_RETN(6);
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
    if (spin_200(e, _o_0, _a_1, _a_2) == 0) {
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
        STK(1) = FID_String_append_k860;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_String_append_k860, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _f_0;
        WL_CONT = term_tsk(FID_String_append_k860, _t_0);
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
  WL_CASE(FID_String_append_k860)
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
  WL_CASE(FID_wire_get_list_5)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_5_k862;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_5_k862, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_5_k862, _t_0);
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
  WL_CASE(FID_wire_get_list_5_k862)
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
          STK(1) = FID_wire_get_list_5_k863;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_5_k863, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_5_k863, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_seen_get_iv)) {
          u64 _t_3 = task_node(e, FID_ffi_doc_seen_get_iv, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_doc_seen_get_iv, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_doc_seen_get_iv);
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
  WL_CASE(FID_wire_get_list_5_k863)
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
  WL_CASE(FID_ffi_workflow_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_workflow_get_req_k869;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_workflow_get_req_k869, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_workflow_get_req_k869, _t_0);
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
  WL_CASE(FID_ffi_workflow_get_req_k869)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_workflow_get_req_k870;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_workflow_get_req_k870, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_workflow_get_req_k870, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_prior)) {
          u64 _t_3 = task_node(e, FID_ffi_workflow_get_prior, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_workflow_get_prior, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_workflow_get_prior);
      } else if (_h_1 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_workflow_get_req_k874;
          WL_PUSHN(1);
        } else {
          u64 _t_10 = task_node(e, FID_ffi_workflow_get_req_k874, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_workflow_get_req_k874, _t_10);
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
        Term _x_0 = (_h_1 - 2);
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = 0;
        r7 = 0;
        r8 = 0;
        WL_RETN(9);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k870)
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    u32 _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_4;
        STK(1) = _h_5;
        STK(2) = FID_ffi_workflow_get_req_k871;
        WL_PUSHN(3);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_workflow_get_req_k871, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_4;
        e.mem[_t_4 + 1] = _h_5;
        WL_CONT = term_tsk(FID_ffi_workflow_get_req_k871, _t_4);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_5 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_6;
        return term_tsk(FID_wire_get_nat, _t_5);
      }
      r0 = _h_6;
      WL_JMP(FID_wire_get_nat);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k871)
    WL_POPN(2);
    u32 _h_10 = STK(0);
    u32 _h_11 = STK(1);
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
        STK(3) = FID_ffi_workflow_get_req_k872;
        WL_PUSHN(4);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_workflow_get_req_k872, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _h_10;
        e.mem[_t_6 + 1] = _h_11;
        e.mem[_t_6 + 2] = _h_8;
        WL_CONT = term_tsk(FID_ffi_workflow_get_req_k872, _t_6);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_7)) {
        u64 _t_7 = task_node(e, FID_wire_get_list_7, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _h_9;
        return term_tsk(FID_wire_get_list_7, _t_7);
      }
      r0 = _h_9;
      WL_JMP(FID_wire_get_list_7);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k872)
    WL_POPN(3);
    u32 _h_15 = STK(0);
    u32 _h_16 = STK(1);
    Term _h_17 = STK(2);
    u32 _h_12 = r0;
    Term _h_13 = r1;
    Term _h_14 = r2;
    WL_OPEN
    if (_h_12 == 0) {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _h_15;
        STK(1) = _h_16;
        STK(2) = _h_17;
        STK(3) = _h_13;
        STK(4) = FID_ffi_workflow_get_req_k873;
        WL_PUSHN(5);
      } else {
        u64 _t_8 = task_node(e, FID_ffi_workflow_get_req_k873, WL_CONT, WL_IDX, 1);
        e.mem[_t_8 + 0] = _h_15;
        e.mem[_t_8 + 1] = _h_16;
        e.mem[_t_8 + 2] = _h_17;
        e.mem[_t_8 + 3] = _h_13;
        WL_CONT = term_tsk(FID_ffi_workflow_get_req_k873, _t_8);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_pool)) {
        u64 _t_9 = task_node(e, FID_ffi_workflow_get_pool, WL_CONT, WL_IDX, 0);
        e.mem[_t_9 + 0] = _h_14;
        return term_tsk(FID_ffi_workflow_get_pool, _t_9);
      }
      r0 = _h_14;
      WL_JMP(FID_ffi_workflow_get_pool);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k873)
    WL_POPN(4);
    u32 _h_22 = STK(0);
    u32 _h_23 = STK(1);
    Term _h_24 = STK(2);
    Term _h_25 = STK(3);
    u32 _h_18 = r0;
    Term _h_19 = r1;
    Term _h_20 = r2;
    Term _h_21 = r3;
    WL_OPEN
    Term _o_0[9];
    if (spin_95(e, _o_0, _h_22, _h_23, _h_24, _h_25, _h_18, _h_19, _h_20, _h_21) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    r6 = _o_0[6];
    r7 = _o_0[7];
    r8 = _o_0[8];
    WL_RETN(9);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k874)
    u32 _h_26 = r0;
    Term _h_27 = r1;
    Term _h_28 = r2;
    WL_OPEN
    if (_h_26 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_27;
        STK(1) = FID_ffi_workflow_get_req_k875;
        WL_PUSHN(2);
      } else {
        u64 _t_12 = task_node(e, FID_ffi_workflow_get_req_k875, WL_CONT, WL_IDX, 1);
        e.mem[_t_12 + 0] = _h_27;
        WL_CONT = term_tsk(FID_ffi_workflow_get_req_k875, _t_12);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_13 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_13 + 0] = _h_28;
        return term_tsk(FID_wire_get_nat, _t_13);
      }
      r0 = _h_28;
      WL_JMP(FID_wire_get_nat);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k875)
    WL_POPN(1);
    Term _h_32 = STK(0);
    u32 _h_29 = r0;
    Term _h_30 = r1;
    Term _h_31 = r2;
    WL_OPEN
    if (_h_29 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_32;
        STK(1) = _h_30;
        STK(2) = FID_ffi_workflow_get_req_k876;
        WL_PUSHN(3);
      } else {
        u64 _t_14 = task_node(e, FID_ffi_workflow_get_req_k876, WL_CONT, WL_IDX, 1);
        e.mem[_t_14 + 0] = _h_32;
        e.mem[_t_14 + 1] = _h_30;
        WL_CONT = term_tsk(FID_ffi_workflow_get_req_k876, _t_14);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_15 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_15 + 0] = _h_31;
        return term_tsk(FID_wire_get_nat, _t_15);
      }
      r0 = _h_31;
      WL_JMP(FID_wire_get_nat);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_workflow_get_req_k876)
    WL_POPN(2);
    Term _h_36 = STK(0);
    Term _h_37 = STK(1);
    u32 _h_33 = r0;
    Term _h_34 = r1;
    Term _h_35 = r2;
    WL_OPEN
    Term _o_1[9];
    if (spin_133(e, _o_1, _h_36, _h_37, _h_33, _h_34, _h_35) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    r6 = _o_1[6];
    r7 = _o_1[7];
    r8 = _o_1[8];
    WL_RETN(9);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_aux_fallback_get_req_k880;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_aux_fallback_get_req_k880, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k880, _t_0);
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
  WL_CASE(FID_ffi_aux_fallback_get_req_k880)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (_h_1 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_req_k881;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_aux_fallback_get_req_k881, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k881, _t_2);
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
          STK(0) = FID_ffi_aux_fallback_get_req_k883;
          WL_PUSHN(1);
        } else {
          u64 _t_6 = task_node(e, FID_ffi_aux_fallback_get_req_k883, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k883, _t_6);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_gate)) {
          u64 _t_7 = task_node(e, FID_ffi_aux_fallback_get_gate, WL_CONT, WL_IDX, 0);
          e.mem[_t_7 + 0] = _h_2;
          return term_tsk(FID_ffi_aux_fallback_get_gate, _t_7);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_aux_fallback_get_gate);
      } else if (_h_1 == 2) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_aux_fallback_get_req_k886;
          WL_PUSHN(1);
        } else {
          u64 _t_12 = task_node(e, FID_ffi_aux_fallback_get_req_k886, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k886, _t_12);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_route)) {
          u64 _t_13 = task_node(e, FID_ffi_aux_fallback_get_route, WL_CONT, WL_IDX, 0);
          e.mem[_t_13 + 0] = _h_2;
          return term_tsk(FID_ffi_aux_fallback_get_route, _t_13);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_aux_fallback_get_route);
      } else {
        Term _c_0 = (_h_1 - 3);
        term_sink(e, _h_2);
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = 0;
        r7 = 0;
        r8 = 0;
        r9 = 0;
        r10 = 0;
        WL_RETN(11);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      r9 = 0;
      r10 = 0;
      WL_RETN(11);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k881)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_4;
        STK(1) = FID_ffi_aux_fallback_get_req_k882;
        WL_PUSHN(2);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_aux_fallback_get_req_k882, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_4;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k882, _t_4);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_sel)) {
        u64 _t_5 = task_node(e, FID_ffi_aux_fallback_get_sel, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_5;
        return term_tsk(FID_ffi_aux_fallback_get_sel, _t_5);
      }
      r0 = _h_5;
      WL_JMP(FID_ffi_aux_fallback_get_sel);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      r9 = 0;
      r10 = 0;
      WL_RETN(11);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k882)
    WL_POPN(1);
    Term _h_10 = STK(0);
    u32 _h_6 = r0;
    u32 _h_7 = r1;
    Term _h_8 = r2;
    Term _h_9 = r3;
    WL_OPEN
    Term _o_0[11];
    if (spin_176(e, _o_0, _h_10, _h_6, _h_7, _h_8, _h_9) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    r6 = _o_0[6];
    r7 = (u32)_o_0[7];
    r8 = _o_0[8];
    r9 = _o_0[9];
    r10 = _o_0[10];
    WL_RETN(11);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k883)
    u32 _h_11 = r0;
    u32 _h_12 = r1;
    Term _h_13 = r2;
    Term _h_14 = r3;
    Term _h_15 = r4;
    Term _h_16 = r5;
    Term _h_17 = r6;
    WL_OPEN
    if (_h_11 == 0) {
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _h_12;
        STK(1) = _h_13;
        STK(2) = _h_14;
        STK(3) = _h_15;
        STK(4) = _h_16;
        STK(5) = FID_ffi_aux_fallback_get_req_k884;
        WL_PUSHN(6);
      } else {
        u64 _t_8 = task_node(e, FID_ffi_aux_fallback_get_req_k884, WL_CONT, WL_IDX, 1);
        e.mem[_t_8 + 0] = _h_12;
        e.mem[_t_8 + 1] = _h_13;
        e.mem[_t_8 + 2] = _h_14;
        e.mem[_t_8 + 3] = _h_15;
        e.mem[_t_8 + 4] = _h_16;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k884, _t_8);
        WL_IDX = 5;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_look)) {
        u64 _t_9 = task_node(e, FID_ffi_aux_fallback_get_look, WL_CONT, WL_IDX, 0);
        e.mem[_t_9 + 0] = _h_17;
        return term_tsk(FID_ffi_aux_fallback_get_look, _t_9);
      }
      r0 = _h_17;
      WL_JMP(FID_ffi_aux_fallback_get_look);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      r9 = 0;
      r10 = 0;
      WL_RETN(11);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k884)
    WL_POPN(5);
    u32 _h_22 = STK(0);
    Term _h_23 = STK(1);
    Term _h_24 = STK(2);
    Term _h_25 = STK(3);
    Term _h_26 = STK(4);
    u32 _h_18 = r0;
    u32 _h_19 = r1;
    Term _h_20 = r2;
    Term _h_21 = r3;
    WL_OPEN
    if (_h_18 == 0) {
      if (seq) {
        WL_ROOM(8, 0);
        STK(0) = _h_22;
        STK(1) = _h_23;
        STK(2) = _h_24;
        STK(3) = _h_25;
        STK(4) = _h_26;
        STK(5) = _h_19;
        STK(6) = _h_20;
        STK(7) = FID_ffi_aux_fallback_get_req_k885;
        WL_PUSHN(8);
      } else {
        u64 _t_10 = task_node(e, FID_ffi_aux_fallback_get_req_k885, WL_CONT, WL_IDX, 1);
        e.mem[_t_10 + 0] = _h_22;
        e.mem[_t_10 + 1] = _h_23;
        e.mem[_t_10 + 2] = _h_24;
        e.mem[_t_10 + 3] = _h_25;
        e.mem[_t_10 + 4] = _h_26;
        e.mem[_t_10 + 5] = _h_19;
        e.mem[_t_10 + 6] = _h_20;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k885, _t_10);
        WL_IDX = 7;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_11 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_11 + 0] = _h_21;
        return term_tsk(FID_wire_get_nat, _t_11);
      }
      r0 = _h_21;
      WL_JMP(FID_wire_get_nat);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      r9 = 0;
      r10 = 0;
      WL_RETN(11);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k885)
    WL_POPN(7);
    u32 _h_30 = STK(0);
    Term _h_31 = STK(1);
    Term _h_32 = STK(2);
    Term _h_33 = STK(3);
    Term _h_34 = STK(4);
    u32 _h_35 = STK(5);
    Term _h_36 = STK(6);
    u32 _h_27 = r0;
    Term _h_28 = r1;
    Term _h_29 = r2;
    WL_OPEN
    Term _o_1[11];
    if (spin_138(e, _o_1, _h_30, _h_31, _h_32, _h_33, _h_34, _h_35, _h_36, _h_27, _h_28, _h_29) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    r6 = _o_1[6];
    r7 = (u32)_o_1[7];
    r8 = _o_1[8];
    r9 = _o_1[9];
    r10 = _o_1[10];
    WL_RETN(11);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k886)
    u32 _h_37 = r0;
    u32 _h_38 = r1;
    Term _h_39 = r2;
    Term _h_40 = r3;
    Term _h_41 = r4;
    Term _h_42 = r5;
    WL_OPEN
    if (_h_37 == 0) {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _h_38;
        STK(1) = _h_39;
        STK(2) = _h_40;
        STK(3) = _h_41;
        STK(4) = FID_ffi_aux_fallback_get_req_k887;
        WL_PUSHN(5);
      } else {
        u64 _t_14 = task_node(e, FID_ffi_aux_fallback_get_req_k887, WL_CONT, WL_IDX, 1);
        e.mem[_t_14 + 0] = _h_38;
        e.mem[_t_14 + 1] = _h_39;
        e.mem[_t_14 + 2] = _h_40;
        e.mem[_t_14 + 3] = _h_41;
        WL_CONT = term_tsk(FID_ffi_aux_fallback_get_req_k887, _t_14);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_1)) {
        u64 _t_15 = task_node(e, FID_wire_get_list_1, WL_CONT, WL_IDX, 0);
        e.mem[_t_15 + 0] = _h_42;
        return term_tsk(FID_wire_get_list_1, _t_15);
      }
      r0 = _h_42;
      WL_JMP(FID_wire_get_list_1);
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      r9 = 0;
      r10 = 0;
      WL_RETN(11);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_aux_fallback_get_req_k887)
    WL_POPN(4);
    u32 _h_46 = STK(0);
    Term _h_47 = STK(1);
    Term _h_48 = STK(2);
    Term _h_49 = STK(3);
    u32 _h_43 = r0;
    Term _h_44 = r1;
    Term _h_45 = r2;
    WL_OPEN
    Term _o_2[11];
    if (spin_175(e, _o_2, _h_46, _h_47, _h_48, _h_49, _h_43, _h_44, _h_45) == 0) {
      return 0;
    }
    r0 = (u32)_o_2[0];
    r1 = (u32)_o_2[1];
    r2 = _o_2[2];
    r3 = _o_2[3];
    r4 = _o_2[4];
    r5 = _o_2[5];
    r6 = _o_2[6];
    r7 = (u32)_o_2[7];
    r8 = _o_2[8];
    r9 = _o_2[9];
    r10 = _o_2[10];
    WL_RETN(11);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_default_model_get_in)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_default_model_get_in_k894;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_default_model_get_in_k894, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_default_model_get_in_k894, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_default_model_get_saved)) {
      u64 _t_1 = task_node(e, FID_ffi_default_model_get_saved, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_ffi_default_model_get_saved, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_ffi_default_model_get_saved);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_default_model_get_in_k894)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      u32 _v_1 = 0;
      Term _v_2 = 0;
      Term _o_0[3];
      if (spin_43(e, _o_0, _h_3) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      _v_1 = (u32)_o_0[1];
      _v_2 = _o_0[2];
      if (_v_0 == 0) {
        u32 _v_3 = 0;
        u32 _v_4 = 0;
        Term _v_5 = 0;
        Term _o_1[3];
        if (spin_43(e, _o_1, _v_2) == 0) {
          return 0;
        }
        _v_3 = (u32)_o_1[0];
        _v_4 = (u32)_o_1[1];
        _v_5 = _o_1[2];
        if (_v_3 == 0) {
          u32 _v_6 = 0;
          u32 _v_7 = 0;
          Term _v_8 = 0;
          Term _o_2[3];
          if (spin_43(e, _o_2, _v_5) == 0) {
            return 0;
          }
          _v_6 = (u32)_o_2[0];
          _v_7 = (u32)_o_2[1];
          _v_8 = _o_2[2];
          if (_v_6 == 0) {
            if (seq) {
              WL_ROOM(6, 0);
              STK(0) = _h_1;
              STK(1) = _h_2;
              STK(2) = _v_1;
              STK(3) = _v_4;
              STK(4) = _v_7;
              STK(5) = FID_ffi_default_model_get_in_k895;
              WL_PUSHN(6);
            } else {
              u64 _t_2 = task_node(e, FID_ffi_default_model_get_in_k895, WL_CONT, WL_IDX, 1);
              e.mem[_t_2 + 0] = _h_1;
              e.mem[_t_2 + 1] = _h_2;
              e.mem[_t_2 + 2] = _v_1;
              e.mem[_t_2 + 3] = _v_4;
              e.mem[_t_2 + 4] = _v_7;
              WL_CONT = term_tsk(FID_ffi_default_model_get_in_k895, _t_2);
              WL_IDX = 5;
            }
            if (!DEVICE && !seq && fid_nofk(FID_ffi_default_model_get_next)) {
              u64 _t_3 = task_node(e, FID_ffi_default_model_get_next, WL_CONT, WL_IDX, 0);
              e.mem[_t_3 + 0] = _v_8;
              return term_tsk(FID_ffi_default_model_get_next, _t_3);
            }
            r0 = _v_8;
            WL_JMP(FID_ffi_default_model_get_next);
          } else {
            r0 = 1;
            r1 = 0;
            r2 = 0;
            r3 = 0;
            r4 = 0;
            r5 = 0;
            r6 = 0;
            r7 = 0;
            r8 = 0;
            WL_RETN(9);
          }
        } else {
          r0 = 1;
          r1 = 0;
          r2 = 0;
          r3 = 0;
          r4 = 0;
          r5 = 0;
          r6 = 0;
          r7 = 0;
          r8 = 0;
          WL_RETN(9);
        }
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = 0;
        r7 = 0;
        r8 = 0;
        WL_RETN(9);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = 0;
      r8 = 0;
      WL_RETN(9);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_default_model_get_in_k895)
    WL_POPN(5);
    u32 _h_8 = STK(0);
    Term _h_9 = STK(1);
    u32 _v_9 = STK(2);
    u32 _v_10 = STK(3);
    u32 _v_11 = STK(4);
    u32 _h_4 = r0;
    u32 _h_5 = r1;
    Term _h_6 = r2;
    Term _h_7 = r3;
    WL_OPEN
    Term _o_3[9];
    if (spin_143(e, _o_3, _h_8, _h_9, _v_9, _v_10, _v_11, _h_4, _h_5, _h_6, _h_7) == 0) {
      return 0;
    }
    r0 = (u32)_o_3[0];
    r1 = (u32)_o_3[1];
    r2 = _o_3[2];
    r3 = (u32)_o_3[3];
    r4 = (u32)_o_3[4];
    r5 = (u32)_o_3[5];
    r6 = (u32)_o_3[6];
    r7 = _o_3[7];
    r8 = _o_3[8];
    WL_RETN(9);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_sandbox_get_doc)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_sandbox_get_doc_k908;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_sandbox_get_doc_k908, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_sandbox_get_doc_k908, _t_0);
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
  WL_CASE(FID_ffi_sandbox_get_doc_k908)
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
          STK(0) = FID_ffi_sandbox_get_doc_k909;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_sandbox_get_doc_k909, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_sandbox_get_doc_k909, _t_2);
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
        Term _q_0 = (_h_1 - 2);
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
  WL_CASE(FID_ffi_sandbox_get_doc_k909)
    u32 _h_3 = r0;
    Term _h_4 = r1;
    Term _h_5 = r2;
    WL_OPEN
    Term _o_0[4];
    if (spin_214(e, _o_0, _h_3, _h_4, _h_5) == 0) {
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
  WL_CASE(FID_wire_get_list_3)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_list_3_k914;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_list_3_k914, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_list_3_k914, _t_0);
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
  WL_CASE(FID_wire_get_list_3_k914)
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
          STK(1) = FID_wire_get_list_3_k915;
          WL_PUSHN(2);
        } else {
          u64 _t_2 = task_node(e, FID_wire_get_list_3_k915, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _m_0;
          WL_CONT = term_tsk(FID_wire_get_list_3_k915, _t_2);
          WL_IDX = 1;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_lines_get_run)) {
          u64 _t_3 = task_node(e, FID_ffi_doc_lines_get_run, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _h_2;
          return term_tsk(FID_ffi_doc_lines_get_run, _t_3);
        }
        r0 = _h_2;
        WL_JMP(FID_ffi_doc_lines_get_run);
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
  WL_CASE(FID_wire_get_list_3_k915)
    WL_POPN(1);
    Term _m_1 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    u32 _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_go_3)) {
      u64 _t_4 = task_node(e, FID_wire_get_list_go_3, WL_CONT, WL_IDX, 0);
      e.mem[_t_4 + 0] = _m_1;
      e.mem[_t_4 + 1] = _h_3;
      e.mem[_t_4 + 2] = _h_4;
      e.mem[_t_4 + 3] = _h_5;
      e.mem[_t_4 + 4] = _h_6;
      e.mem[_t_4 + 5] = _h_7;
      return term_tsk(FID_wire_get_list_go_3, _t_4);
    }
    r0 = _m_1;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    WL_JMP(FID_wire_get_list_go_3);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_wire_get_nat)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_wire_get_nat_k930;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_wire_get_nat_k930, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_wire_get_nat_k930, _t_0);
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
  WL_CASE(FID_wire_get_nat_k930)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_wire_get_nat_k931;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_wire_get_nat_k931, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_wire_get_nat_k931, _t_2);
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
  WL_CASE(FID_wire_get_nat_k931)
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
        e.mem[_t_4 + 3] = term_ctr(CID_Con, STAT_OFF + 628);
        return term_tsk(FID_wire_get_nat_end, _t_4);
      }
      r0 = _h_3;
      r1 = _h_4;
      r2 = _h_5;
      r3 = term_ctr(CID_Con, STAT_OFF + 628);
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
  WL_CASE(FID_ffi_admission_get_open)
    Term _s_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_admission_get_open_k938;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_admission_get_open_k938, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_admission_get_open_k938, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_get_lim)) {
      u64 _t_1 = task_node(e, FID_ffi_admission_get_lim, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _s_0;
      return term_tsk(FID_ffi_admission_get_lim, _t_1);
    }
    r0 = _s_0;
    WL_JMP(FID_ffi_admission_get_lim);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_get_open_k938)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_1;
        STK(1) = _h_2;
        STK(2) = FID_ffi_admission_get_open_k939;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_admission_get_open_k939, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        e.mem[_t_2 + 1] = _h_2;
        WL_CONT = term_tsk(FID_ffi_admission_get_open_k939, _t_2);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_3 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_3;
        return term_tsk(FID_wire_get_nat, _t_3);
      }
      r0 = _h_3;
      WL_JMP(FID_wire_get_nat);
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
  WL_CASE(FID_ffi_admission_get_open_k939)
    WL_POPN(2);
    u32 _h_7 = STK(0);
    Term _h_8 = STK(1);
    u32 _h_4 = r0;
    Term _h_5 = r1;
    Term _h_6 = r2;
    WL_OPEN
    Term _o_0[5];
    if (spin_227(e, _o_0, _h_7, _h_8, _h_4, _h_5, _h_6) == 0) {
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
  WL_CASE(FID_ffi_admission_step)
    u32 _st_0 = r0;
    u32 _st_1 = r1;
    Term _st_2 = r2;
    Term _st_3 = r3;
    Term _st_4 = r4;
    Term _st_5 = r5;
    Term _input_0 = r6;
    WL_OPEN
    if (_st_0 == 0) {
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _st_1;
        STK(1) = _st_2;
        STK(2) = _st_3;
        STK(3) = _st_4;
        STK(4) = _st_5;
        STK(5) = FID_ffi_admission_step_k945;
        WL_PUSHN(6);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_admission_step_k945, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _st_1;
        e.mem[_t_0 + 1] = _st_2;
        e.mem[_t_0 + 2] = _st_3;
        e.mem[_t_0 + 3] = _st_4;
        e.mem[_t_0 + 4] = _st_5;
        WL_CONT = term_tsk(FID_ffi_admission_step_k945, _t_0);
        WL_IDX = 5;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_get_op)) {
        u64 _t_1 = task_node(e, FID_ffi_admission_get_op, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_ffi_admission_get_op, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_admission_get_op);
    } else {
      term_sink(e, _input_0);
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = term_ctr(CID_SCon, STAT_OFF + 1458);
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_step_k945)
    WL_POPN(5);
    u32 _st_6 = STK(0);
    Term _st_7 = STK(1);
    Term _st_8 = STK(2);
    Term _st_9 = STK(3);
    Term _st_10 = STK(4);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    Term _h_5 = r5;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_77(e, _o_0, _h_5) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      if (_v_0 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_admission_step_k946;
          WL_PUSHN(1);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_admission_step_k946, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_admission_step_k946, _t_2);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_admission_Live_step)) {
          u64 _t_3 = task_node(e, FID_admission_Live_step, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _st_6;
          e.mem[_t_3 + 1] = _st_7;
          e.mem[_t_3 + 2] = _st_8;
          e.mem[_t_3 + 3] = _st_9;
          e.mem[_t_3 + 4] = _st_10;
          e.mem[_t_3 + 5] = _h_1;
          e.mem[_t_3 + 6] = _h_2;
          e.mem[_t_3 + 7] = _h_3;
          e.mem[_t_3 + 8] = _h_4;
          return term_tsk(FID_admission_Live_step, _t_3);
        }
        r0 = _st_6;
        r1 = _st_7;
        r2 = _st_8;
        r3 = _st_9;
        r4 = _st_10;
        r5 = _h_1;
        r6 = _h_2;
        r7 = _h_3;
        r8 = _h_4;
        WL_JMP(FID_admission_Live_step);
      } else {
        r0 = 0;
        r1 = _st_6;
        r2 = _st_7;
        r3 = _st_8;
        r4 = _st_9;
        r5 = _st_10;
        r6 = term_ctr(CID_SCon, STAT_OFF + 672);
        WL_RETN(7);
      }
    } else {
      r0 = 0;
      r1 = _st_6;
      r2 = _st_7;
      r3 = _st_8;
      r4 = _st_9;
      r5 = _st_10;
      r6 = term_ctr(CID_SCon, STAT_OFF + 994);
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_step_k946)
    u32 _y_0 = r0;
    Term _y_1 = r1;
    Term _y_2 = r2;
    Term _y_3 = r3;
    Term _y_4 = r4;
    WL_OPEN
    if (seq) {
      WL_ROOM(6, 0);
      STK(0) = _y_0;
      STK(1) = _y_1;
      STK(2) = _y_2;
      STK(3) = _y_3;
      STK(4) = _y_4;
      STK(5) = FID_ffi_admission_step_k947;
      WL_PUSHN(6);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_admission_step_k947, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _y_0;
      e.mem[_t_4 + 1] = _y_1;
      e.mem[_t_4 + 2] = _y_2;
      e.mem[_t_4 + 3] = _y_3;
      e.mem[_t_4 + 4] = _y_4;
      WL_CONT = term_tsk(FID_ffi_admission_step_k947, _t_4);
      WL_IDX = 5;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_put_live)) {
      u64 _t_5 = task_node(e, FID_ffi_admission_put_live, WL_CONT, WL_IDX, 0);
      e.mem[_t_5 + 0] = _y_0;
      e.mem[_t_5 + 1] = _y_1;
      e.mem[_t_5 + 2] = _y_2;
      e.mem[_t_5 + 3] = _y_3;
      e.mem[_t_5 + 4] = _y_4;
      e.mem[_t_5 + 5] = term_pak(CID_SNil, 0);
      return term_tsk(FID_ffi_admission_put_live, _t_5);
    }
    r0 = _y_0;
    r1 = _y_1;
    r2 = _y_2;
    r3 = _y_3;
    r4 = _y_4;
    r5 = term_pak(CID_SNil, 0);
    WL_JMP(FID_ffi_admission_put_live);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_step_k947)
    WL_POPN(5);
    u32 _y_5 = STK(0);
    Term _y_6 = STK(1);
    Term _y_7 = STK(2);
    Term _y_8 = STK(3);
    Term _y_9 = STK(4);
    Term _h_6 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _y_5;
    r2 = _y_6;
    r3 = _y_7;
    r4 = _y_8;
    r5 = _y_9;
    r6 = _h_6;
    WL_RETN(7);
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
        STK(3) = FID_ffi_echo_step_k950;
        WL_PUSHN(4);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_echo_step_k950, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _s_1;
        e.mem[_t_0 + 1] = _s_2;
        e.mem[_t_0 + 2] = _input_0;
        WL_CONT = term_tsk(FID_ffi_echo_step_k950, _t_0);
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
      r3 = term_ctr(CID_SCon, STAT_OFF + 1472);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k950)
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
      STK(3) = FID_ffi_echo_step_k951;
      WL_PUSHN(4);
    } else {
      u64 _t_2 = task_node(e, FID_ffi_echo_step_k951, WL_CONT, WL_IDX, 1);
      e.mem[_t_2 + 0] = _s_3;
      e.mem[_t_2 + 1] = _input_1;
      e.mem[_t_2 + 2] = _h_0;
      WL_CONT = term_tsk(FID_ffi_echo_step_k951, _t_2);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_String_append)) {
      u64 _t_3 = task_node(e, FID_String_append, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = term_ctr(CID_SCon, STAT_OFF + 1460);
      e.mem[_t_3 + 1] = _s_4;
      return term_tsk(FID_String_append, _t_3);
    }
    r0 = term_ctr(CID_SCon, STAT_OFF + 1460);
    r1 = _s_4;
    WL_JMP(FID_String_append);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_step_k951)
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
      STK(2) = FID_ffi_echo_step_k952;
      WL_PUSHN(3);
    } else {
      u64 _t_4 = task_node(e, FID_ffi_echo_step_k952, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _s_5;
      e.mem[_t_4 + 1] = _input_2;
      WL_CONT = term_tsk(FID_ffi_echo_step_k952, _t_4);
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
  WL_CASE(FID_ffi_echo_step_k952)
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
  WL_CASE(FID_ffi_admission_open)
    Term _input_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_admission_open_k1009;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_admission_open_k1009, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_admission_open_k1009, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_get_open)) {
      u64 _t_1 = task_node(e, FID_ffi_admission_get_open, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _input_0;
      return term_tsk(FID_ffi_admission_get_open, _t_1);
    }
    r0 = _input_0;
    WL_JMP(FID_ffi_admission_get_open);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_open_k1009)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    Term _h_4 = r4;
    WL_OPEN
    if (_h_0 == 0) {
      u32 _v_0 = 0;
      Term _o_0[1];
      if (spin_77(e, _o_0, _h_4) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_0[0];
      if (_v_0 == 1) {
        u32 _v_1 = 0;
        Term _v_2 = 0;
        Term _v_3 = 0;
        Term _v_4 = 0;
        Term _v_5 = 0;
        Term _o_1[5];
        if (spin_220(e, _o_1, _h_1, _h_2, _h_3) == 0) {
          return 0;
        }
        _v_1 = (u32)_o_1[0];
        _v_2 = _o_1[1];
        _v_3 = _o_1[2];
        _v_4 = _o_1[3];
        _v_5 = _o_1[4];
        if (seq) {
          WL_ROOM(6, 0);
          STK(0) = _v_1;
          STK(1) = _v_2;
          STK(2) = _v_3;
          STK(3) = _v_4;
          STK(4) = _v_5;
          STK(5) = FID_ffi_admission_open_k1010;
          WL_PUSHN(6);
        } else {
          u64 _t_2 = task_node(e, FID_ffi_admission_open_k1010, WL_CONT, WL_IDX, 1);
          e.mem[_t_2 + 0] = _v_1;
          e.mem[_t_2 + 1] = _v_2;
          e.mem[_t_2 + 2] = _v_3;
          e.mem[_t_2 + 3] = _v_4;
          e.mem[_t_2 + 4] = _v_5;
          WL_CONT = term_tsk(FID_ffi_admission_open_k1010, _t_2);
          WL_IDX = 5;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_put_live)) {
          u64 _t_3 = task_node(e, FID_ffi_admission_put_live, WL_CONT, WL_IDX, 0);
          e.mem[_t_3 + 0] = _v_1;
          e.mem[_t_3 + 1] = _v_2;
          e.mem[_t_3 + 2] = _v_3;
          e.mem[_t_3 + 3] = _v_4;
          e.mem[_t_3 + 4] = _v_5;
          e.mem[_t_3 + 5] = term_pak(CID_SNil, 0);
          return term_tsk(FID_ffi_admission_put_live, _t_3);
        }
        r0 = _v_1;
        r1 = _v_2;
        r2 = _v_3;
        r3 = _v_4;
        r4 = _v_5;
        r5 = term_pak(CID_SNil, 0);
        WL_JMP(FID_ffi_admission_put_live);
      } else {
        r0 = 1;
        r1 = 0;
        r2 = 0;
        r3 = 0;
        r4 = 0;
        r5 = 0;
        r6 = term_ctr(CID_SCon, STAT_OFF + 672);
        WL_RETN(7);
      }
    } else {
      r0 = 1;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = term_ctr(CID_SCon, STAT_OFF + 1330);
      WL_RETN(7);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_admission_open_k1010)
    WL_POPN(5);
    u32 _v_6 = STK(0);
    Term _v_7 = STK(1);
    Term _v_8 = STK(2);
    Term _v_9 = STK(3);
    Term _v_10 = STK(4);
    Term _h_5 = r0;
    WL_OPEN
    r0 = 0;
    r1 = _v_6;
    r2 = _v_7;
    r3 = _v_8;
    r4 = _v_9;
    r5 = _v_10;
    r6 = _h_5;
    WL_RETN(7);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_open)
    Term _input_0 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_echo_open_k1014;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_echo_open_k1014, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_echo_open_k1014, _t_0);
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
  WL_CASE(FID_ffi_echo_open_k1014)
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    if (_h_0 == 1) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_echo_open_k1015;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_echo_open_k1015, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_echo_open_k1015, _t_2);
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
      r3 = term_ctr(CID_SCon, STAT_OFF + 1394);
      WL_RETN(4);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_echo_open_k1015)
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
    Term _state_4 = r4;
    Term _state_5 = r5;
    Term _state_6 = r6;
    Term _input_0 = r7;
    WL_OPEN
    if (_state_0 == 0) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_step_go_k1018;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_step_go_k1018, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_step_go_k1018, _t_0);
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
        STK(0) = FID_step_go_k1019;
        WL_PUSHN(1);
      } else {
        u64 _t_2 = task_node(e, FID_step_go_k1019, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_step_go_k1019, _t_2);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_step)) {
        u64 _t_3 = task_node(e, FID_ffi_admission_step, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _state_1;
        e.mem[_t_3 + 1] = _state_2;
        e.mem[_t_3 + 2] = _state_3;
        e.mem[_t_3 + 3] = _state_4;
        e.mem[_t_3 + 4] = _state_5;
        e.mem[_t_3 + 5] = _state_6;
        e.mem[_t_3 + 6] = _input_0;
        return term_tsk(FID_ffi_admission_step, _t_3);
      }
      r0 = _state_1;
      r1 = _state_2;
      r2 = _state_3;
      r3 = _state_4;
      r4 = _state_5;
      r5 = _state_6;
      r6 = _input_0;
      WL_JMP(FID_ffi_admission_step);
    } else {
      term_sink(e, _input_0);
      r0 = 2;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = term_ctr(CID_SCon, STAT_OFF + 1498);
      WL_RETN(8);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_go_k1018)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_0[8];
    if (spin_230(e, _o_0, _h_0, _h_1, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    r6 = _o_0[6];
    r7 = _o_0[7];
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_go_k1019)
    u32 _h_4 = r0;
    u32 _h_5 = r1;
    Term _h_6 = r2;
    Term _h_7 = r3;
    Term _h_8 = r4;
    Term _h_9 = r5;
    Term _h_10 = r6;
    WL_OPEN
    Term _o_1[8];
    if (spin_231(e, _o_1, _h_4, _h_5, _h_6, _h_7, _h_8, _h_9, _h_10) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    r6 = _o_1[6];
    r7 = _o_1[7];
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go)
    u32 _entry_0 = r0;
    Term _input_0 = r1;
    WL_OPEN
    if (_entry_0 == 0) {
      Term _o_0[1];
      if (spin_232(e, _o_0, _input_0) == 0) {
        return 0;
      }
      r0 = _o_0[0];
      WL_RETN(1);
    } else if ((_entry_0 & 15) == 0) {
      u32 _16_0 = ((_entry_0 >> 4) & 1);
      u32 _17_0 = ((_entry_0 >> 5) & 1);
      u32 _17_1 = ((_entry_0 >> 6) & 1);
      u32 _17_2 = ((_entry_0 >> 7) & 1);
      u32 _17_3 = ((_entry_0 >> 8) & 1);
      u32 _17_4 = ((_entry_0 >> 9) & 1);
      u32 _17_5 = ((_entry_0 >> 10) & 1);
      u32 _17_6 = ((_entry_0 >> 11) & 1);
      u32 _17_7 = ((_entry_0 >> 12) & 1);
      u32 _17_8 = ((_entry_0 >> 13) & 1);
      u32 _17_9 = ((_entry_0 >> 14) & 1);
      u32 _17_10 = ((_entry_0 >> 15) & 1);
      u32 _17_11 = ((_entry_0 >> 16) & 1);
      u32 _17_12 = ((_entry_0 >> 17) & 1);
      u32 _17_13 = ((_entry_0 >> 18) & 1);
      u32 _17_14 = ((_entry_0 >> 19) & 1);
      u32 _17_15 = ((_entry_0 >> 20) & 1);
      u32 _17_16 = ((_entry_0 >> 21) & 1);
      u32 _17_17 = ((_entry_0 >> 22) & 1);
      u32 _17_18 = ((_entry_0 >> 23) & 1);
      u32 _17_19 = ((_entry_0 >> 24) & 1);
      u32 _17_20 = ((_entry_0 >> 25) & 1);
      u32 _17_21 = ((_entry_0 >> 26) & 1);
      u32 _17_22 = ((_entry_0 >> 27) & 1);
      u32 _17_23 = ((_entry_0 >> 28) & 1);
      u32 _17_24 = ((_entry_0 >> 29) & 1);
      u32 _17_25 = ((_entry_0 >> 30) & 1);
      u32 _17_26 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_1[1];
      if (spin_51(e, _o_1, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_1[0];
      WL_RETN(1);
    } else if (_entry_0 == 8) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1022;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_ffi_go_k1022, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1022, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_1 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else if ((_entry_0 & 15) == 8) {
      u32 _72_0 = ((_entry_0 >> 4) & 1);
      u32 _73_0 = ((_entry_0 >> 5) & 1);
      u32 _73_1 = ((_entry_0 >> 6) & 1);
      u32 _73_2 = ((_entry_0 >> 7) & 1);
      u32 _73_3 = ((_entry_0 >> 8) & 1);
      u32 _73_4 = ((_entry_0 >> 9) & 1);
      u32 _73_5 = ((_entry_0 >> 10) & 1);
      u32 _73_6 = ((_entry_0 >> 11) & 1);
      u32 _73_7 = ((_entry_0 >> 12) & 1);
      u32 _73_8 = ((_entry_0 >> 13) & 1);
      u32 _73_9 = ((_entry_0 >> 14) & 1);
      u32 _73_10 = ((_entry_0 >> 15) & 1);
      u32 _73_11 = ((_entry_0 >> 16) & 1);
      u32 _73_12 = ((_entry_0 >> 17) & 1);
      u32 _73_13 = ((_entry_0 >> 18) & 1);
      u32 _73_14 = ((_entry_0 >> 19) & 1);
      u32 _73_15 = ((_entry_0 >> 20) & 1);
      u32 _73_16 = ((_entry_0 >> 21) & 1);
      u32 _73_17 = ((_entry_0 >> 22) & 1);
      u32 _73_18 = ((_entry_0 >> 23) & 1);
      u32 _73_19 = ((_entry_0 >> 24) & 1);
      u32 _73_20 = ((_entry_0 >> 25) & 1);
      u32 _73_21 = ((_entry_0 >> 26) & 1);
      u32 _73_22 = ((_entry_0 >> 27) & 1);
      u32 _73_23 = ((_entry_0 >> 28) & 1);
      u32 _73_24 = ((_entry_0 >> 29) & 1);
      u32 _73_25 = ((_entry_0 >> 30) & 1);
      u32 _73_26 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_11[1];
      if (spin_51(e, _o_11, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_11[0];
      WL_RETN(1);
    } else if (_entry_0 == 4) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1027;
        WL_PUSHN(1);
      } else {
        u64 _t_10 = task_node(e, FID_ffi_go_k1027, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1027, _t_10);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_11 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_11 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_11);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else if ((_entry_0 & 7) == 4) {
      u32 _128_0 = ((_entry_0 >> 3) & 1);
      u32 _129_0 = ((_entry_0 >> 4) & 1);
      u32 _129_1 = ((_entry_0 >> 5) & 1);
      u32 _129_2 = ((_entry_0 >> 6) & 1);
      u32 _129_3 = ((_entry_0 >> 7) & 1);
      u32 _129_4 = ((_entry_0 >> 8) & 1);
      u32 _129_5 = ((_entry_0 >> 9) & 1);
      u32 _129_6 = ((_entry_0 >> 10) & 1);
      u32 _129_7 = ((_entry_0 >> 11) & 1);
      u32 _129_8 = ((_entry_0 >> 12) & 1);
      u32 _129_9 = ((_entry_0 >> 13) & 1);
      u32 _129_10 = ((_entry_0 >> 14) & 1);
      u32 _129_11 = ((_entry_0 >> 15) & 1);
      u32 _129_12 = ((_entry_0 >> 16) & 1);
      u32 _129_13 = ((_entry_0 >> 17) & 1);
      u32 _129_14 = ((_entry_0 >> 18) & 1);
      u32 _129_15 = ((_entry_0 >> 19) & 1);
      u32 _129_16 = ((_entry_0 >> 20) & 1);
      u32 _129_17 = ((_entry_0 >> 21) & 1);
      u32 _129_18 = ((_entry_0 >> 22) & 1);
      u32 _129_19 = ((_entry_0 >> 23) & 1);
      u32 _129_20 = ((_entry_0 >> 24) & 1);
      u32 _129_21 = ((_entry_0 >> 25) & 1);
      u32 _129_22 = ((_entry_0 >> 26) & 1);
      u32 _129_23 = ((_entry_0 >> 27) & 1);
      u32 _129_24 = ((_entry_0 >> 28) & 1);
      u32 _129_25 = ((_entry_0 >> 29) & 1);
      u32 _129_26 = ((_entry_0 >> 30) & 1);
      u32 _129_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_25[1];
      if (spin_51(e, _o_25, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_25[0];
      WL_RETN(1);
    } else if (_entry_0 == 6) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1036;
        WL_PUSHN(1);
      } else {
        u64 _t_28 = task_node(e, FID_ffi_go_k1036, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1036, _t_28);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_3)) {
        u64 _t_29 = task_node(e, FID_wire_get_list_3, WL_CONT, WL_IDX, 0);
        e.mem[_t_29 + 0] = _input_0;
        return term_tsk(FID_wire_get_list_3, _t_29);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_list_3);
    } else if ((_entry_0 & 7) == 6) {
      u32 _188_0 = ((_entry_0 >> 3) & 1);
      u32 _189_0 = ((_entry_0 >> 4) & 1);
      u32 _189_1 = ((_entry_0 >> 5) & 1);
      u32 _189_2 = ((_entry_0 >> 6) & 1);
      u32 _189_3 = ((_entry_0 >> 7) & 1);
      u32 _189_4 = ((_entry_0 >> 8) & 1);
      u32 _189_5 = ((_entry_0 >> 9) & 1);
      u32 _189_6 = ((_entry_0 >> 10) & 1);
      u32 _189_7 = ((_entry_0 >> 11) & 1);
      u32 _189_8 = ((_entry_0 >> 12) & 1);
      u32 _189_9 = ((_entry_0 >> 13) & 1);
      u32 _189_10 = ((_entry_0 >> 14) & 1);
      u32 _189_11 = ((_entry_0 >> 15) & 1);
      u32 _189_12 = ((_entry_0 >> 16) & 1);
      u32 _189_13 = ((_entry_0 >> 17) & 1);
      u32 _189_14 = ((_entry_0 >> 18) & 1);
      u32 _189_15 = ((_entry_0 >> 19) & 1);
      u32 _189_16 = ((_entry_0 >> 20) & 1);
      u32 _189_17 = ((_entry_0 >> 21) & 1);
      u32 _189_18 = ((_entry_0 >> 22) & 1);
      u32 _189_19 = ((_entry_0 >> 23) & 1);
      u32 _189_20 = ((_entry_0 >> 24) & 1);
      u32 _189_21 = ((_entry_0 >> 25) & 1);
      u32 _189_22 = ((_entry_0 >> 26) & 1);
      u32 _189_23 = ((_entry_0 >> 27) & 1);
      u32 _189_24 = ((_entry_0 >> 28) & 1);
      u32 _189_25 = ((_entry_0 >> 29) & 1);
      u32 _189_26 = ((_entry_0 >> 30) & 1);
      u32 _189_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_31[1];
      if (spin_51(e, _o_31, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_31[0];
      WL_RETN(1);
    } else if (_entry_0 == 10) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1040;
        WL_PUSHN(1);
      } else {
        u64 _t_36 = task_node(e, FID_ffi_go_k1040, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1040, _t_36);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_sandbox_get_doc)) {
        u64 _t_37 = task_node(e, FID_ffi_sandbox_get_doc, WL_CONT, WL_IDX, 0);
        e.mem[_t_37 + 0] = _input_0;
        return term_tsk(FID_ffi_sandbox_get_doc, _t_37);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_sandbox_get_doc);
    } else if ((_entry_0 & 7) == 2) {
      u32 _246_0 = ((_entry_0 >> 3) & 1);
      u32 _247_0 = ((_entry_0 >> 4) & 1);
      u32 _247_1 = ((_entry_0 >> 5) & 1);
      u32 _247_2 = ((_entry_0 >> 6) & 1);
      u32 _247_3 = ((_entry_0 >> 7) & 1);
      u32 _247_4 = ((_entry_0 >> 8) & 1);
      u32 _247_5 = ((_entry_0 >> 9) & 1);
      u32 _247_6 = ((_entry_0 >> 10) & 1);
      u32 _247_7 = ((_entry_0 >> 11) & 1);
      u32 _247_8 = ((_entry_0 >> 12) & 1);
      u32 _247_9 = ((_entry_0 >> 13) & 1);
      u32 _247_10 = ((_entry_0 >> 14) & 1);
      u32 _247_11 = ((_entry_0 >> 15) & 1);
      u32 _247_12 = ((_entry_0 >> 16) & 1);
      u32 _247_13 = ((_entry_0 >> 17) & 1);
      u32 _247_14 = ((_entry_0 >> 18) & 1);
      u32 _247_15 = ((_entry_0 >> 19) & 1);
      u32 _247_16 = ((_entry_0 >> 20) & 1);
      u32 _247_17 = ((_entry_0 >> 21) & 1);
      u32 _247_18 = ((_entry_0 >> 22) & 1);
      u32 _247_19 = ((_entry_0 >> 23) & 1);
      u32 _247_20 = ((_entry_0 >> 24) & 1);
      u32 _247_21 = ((_entry_0 >> 25) & 1);
      u32 _247_22 = ((_entry_0 >> 26) & 1);
      u32 _247_23 = ((_entry_0 >> 27) & 1);
      u32 _247_24 = ((_entry_0 >> 28) & 1);
      u32 _247_25 = ((_entry_0 >> 29) & 1);
      u32 _247_26 = ((_entry_0 >> 30) & 1);
      u32 _247_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_35[1];
      if (spin_51(e, _o_35, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_35[0];
      WL_RETN(1);
    } else if (_entry_0 == 1) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1043;
        WL_PUSHN(1);
      } else {
        u64 _t_42 = task_node(e, FID_ffi_go_k1043, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1043, _t_42);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_43 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_43 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_43);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else if ((_entry_0 & 15) == 1) {
      u32 _310_0 = ((_entry_0 >> 4) & 1);
      u32 _311_0 = ((_entry_0 >> 5) & 1);
      u32 _311_1 = ((_entry_0 >> 6) & 1);
      u32 _311_2 = ((_entry_0 >> 7) & 1);
      u32 _311_3 = ((_entry_0 >> 8) & 1);
      u32 _311_4 = ((_entry_0 >> 9) & 1);
      u32 _311_5 = ((_entry_0 >> 10) & 1);
      u32 _311_6 = ((_entry_0 >> 11) & 1);
      u32 _311_7 = ((_entry_0 >> 12) & 1);
      u32 _311_8 = ((_entry_0 >> 13) & 1);
      u32 _311_9 = ((_entry_0 >> 14) & 1);
      u32 _311_10 = ((_entry_0 >> 15) & 1);
      u32 _311_11 = ((_entry_0 >> 16) & 1);
      u32 _311_12 = ((_entry_0 >> 17) & 1);
      u32 _311_13 = ((_entry_0 >> 18) & 1);
      u32 _311_14 = ((_entry_0 >> 19) & 1);
      u32 _311_15 = ((_entry_0 >> 20) & 1);
      u32 _311_16 = ((_entry_0 >> 21) & 1);
      u32 _311_17 = ((_entry_0 >> 22) & 1);
      u32 _311_18 = ((_entry_0 >> 23) & 1);
      u32 _311_19 = ((_entry_0 >> 24) & 1);
      u32 _311_20 = ((_entry_0 >> 25) & 1);
      u32 _311_21 = ((_entry_0 >> 26) & 1);
      u32 _311_22 = ((_entry_0 >> 27) & 1);
      u32 _311_23 = ((_entry_0 >> 28) & 1);
      u32 _311_24 = ((_entry_0 >> 29) & 1);
      u32 _311_25 = ((_entry_0 >> 30) & 1);
      u32 _311_26 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_46[1];
      if (spin_51(e, _o_46, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_46[0];
      WL_RETN(1);
    } else if (_entry_0 == 9) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1049;
        WL_PUSHN(1);
      } else {
        u64 _t_54 = task_node(e, FID_ffi_go_k1049, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1049, _t_54);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_55 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_55 + 0] = _input_0;
        return term_tsk(FID_wire_get_nat, _t_55);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_nat);
    } else if ((_entry_0 & 15) == 9) {
      u32 _366_0 = ((_entry_0 >> 4) & 1);
      u32 _367_0 = ((_entry_0 >> 5) & 1);
      u32 _367_1 = ((_entry_0 >> 6) & 1);
      u32 _367_2 = ((_entry_0 >> 7) & 1);
      u32 _367_3 = ((_entry_0 >> 8) & 1);
      u32 _367_4 = ((_entry_0 >> 9) & 1);
      u32 _367_5 = ((_entry_0 >> 10) & 1);
      u32 _367_6 = ((_entry_0 >> 11) & 1);
      u32 _367_7 = ((_entry_0 >> 12) & 1);
      u32 _367_8 = ((_entry_0 >> 13) & 1);
      u32 _367_9 = ((_entry_0 >> 14) & 1);
      u32 _367_10 = ((_entry_0 >> 15) & 1);
      u32 _367_11 = ((_entry_0 >> 16) & 1);
      u32 _367_12 = ((_entry_0 >> 17) & 1);
      u32 _367_13 = ((_entry_0 >> 18) & 1);
      u32 _367_14 = ((_entry_0 >> 19) & 1);
      u32 _367_15 = ((_entry_0 >> 20) & 1);
      u32 _367_16 = ((_entry_0 >> 21) & 1);
      u32 _367_17 = ((_entry_0 >> 22) & 1);
      u32 _367_18 = ((_entry_0 >> 23) & 1);
      u32 _367_19 = ((_entry_0 >> 24) & 1);
      u32 _367_20 = ((_entry_0 >> 25) & 1);
      u32 _367_21 = ((_entry_0 >> 26) & 1);
      u32 _367_22 = ((_entry_0 >> 27) & 1);
      u32 _367_23 = ((_entry_0 >> 28) & 1);
      u32 _367_24 = ((_entry_0 >> 29) & 1);
      u32 _367_25 = ((_entry_0 >> 30) & 1);
      u32 _367_26 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_51[1];
      if (spin_51(e, _o_51, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_51[0];
      WL_RETN(1);
    } else if (_entry_0 == 5) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1053;
        WL_PUSHN(1);
      } else {
        u64 _t_62 = task_node(e, FID_ffi_go_k1053, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1053, _t_62);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_default_model_get_in)) {
        u64 _t_63 = task_node(e, FID_ffi_default_model_get_in, WL_CONT, WL_IDX, 0);
        e.mem[_t_63 + 0] = _input_0;
        return term_tsk(FID_ffi_default_model_get_in, _t_63);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_default_model_get_in);
    } else if ((_entry_0 & 7) == 5) {
      u32 _422_0 = ((_entry_0 >> 3) & 1);
      u32 _423_0 = ((_entry_0 >> 4) & 1);
      u32 _423_1 = ((_entry_0 >> 5) & 1);
      u32 _423_2 = ((_entry_0 >> 6) & 1);
      u32 _423_3 = ((_entry_0 >> 7) & 1);
      u32 _423_4 = ((_entry_0 >> 8) & 1);
      u32 _423_5 = ((_entry_0 >> 9) & 1);
      u32 _423_6 = ((_entry_0 >> 10) & 1);
      u32 _423_7 = ((_entry_0 >> 11) & 1);
      u32 _423_8 = ((_entry_0 >> 12) & 1);
      u32 _423_9 = ((_entry_0 >> 13) & 1);
      u32 _423_10 = ((_entry_0 >> 14) & 1);
      u32 _423_11 = ((_entry_0 >> 15) & 1);
      u32 _423_12 = ((_entry_0 >> 16) & 1);
      u32 _423_13 = ((_entry_0 >> 17) & 1);
      u32 _423_14 = ((_entry_0 >> 18) & 1);
      u32 _423_15 = ((_entry_0 >> 19) & 1);
      u32 _423_16 = ((_entry_0 >> 20) & 1);
      u32 _423_17 = ((_entry_0 >> 21) & 1);
      u32 _423_18 = ((_entry_0 >> 22) & 1);
      u32 _423_19 = ((_entry_0 >> 23) & 1);
      u32 _423_20 = ((_entry_0 >> 24) & 1);
      u32 _423_21 = ((_entry_0 >> 25) & 1);
      u32 _423_22 = ((_entry_0 >> 26) & 1);
      u32 _423_23 = ((_entry_0 >> 27) & 1);
      u32 _423_24 = ((_entry_0 >> 28) & 1);
      u32 _423_25 = ((_entry_0 >> 29) & 1);
      u32 _423_26 = ((_entry_0 >> 30) & 1);
      u32 _423_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_53[1];
      if (spin_51(e, _o_53, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_53[0];
      WL_RETN(1);
    } else if (_entry_0 == 3) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1054;
        WL_PUSHN(1);
      } else {
        u64 _t_64 = task_node(e, FID_ffi_go_k1054, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1054, _t_64);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_aux_fallback_get_req)) {
        u64 _t_65 = task_node(e, FID_ffi_aux_fallback_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_65 + 0] = _input_0;
        return term_tsk(FID_ffi_aux_fallback_get_req, _t_65);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_aux_fallback_get_req);
    } else if ((_entry_0 & 15) == 3) {
      u32 _484_0 = ((_entry_0 >> 4) & 1);
      u32 _485_0 = ((_entry_0 >> 5) & 1);
      u32 _485_1 = ((_entry_0 >> 6) & 1);
      u32 _485_2 = ((_entry_0 >> 7) & 1);
      u32 _485_3 = ((_entry_0 >> 8) & 1);
      u32 _485_4 = ((_entry_0 >> 9) & 1);
      u32 _485_5 = ((_entry_0 >> 10) & 1);
      u32 _485_6 = ((_entry_0 >> 11) & 1);
      u32 _485_7 = ((_entry_0 >> 12) & 1);
      u32 _485_8 = ((_entry_0 >> 13) & 1);
      u32 _485_9 = ((_entry_0 >> 14) & 1);
      u32 _485_10 = ((_entry_0 >> 15) & 1);
      u32 _485_11 = ((_entry_0 >> 16) & 1);
      u32 _485_12 = ((_entry_0 >> 17) & 1);
      u32 _485_13 = ((_entry_0 >> 18) & 1);
      u32 _485_14 = ((_entry_0 >> 19) & 1);
      u32 _485_15 = ((_entry_0 >> 20) & 1);
      u32 _485_16 = ((_entry_0 >> 21) & 1);
      u32 _485_17 = ((_entry_0 >> 22) & 1);
      u32 _485_18 = ((_entry_0 >> 23) & 1);
      u32 _485_19 = ((_entry_0 >> 24) & 1);
      u32 _485_20 = ((_entry_0 >> 25) & 1);
      u32 _485_21 = ((_entry_0 >> 26) & 1);
      u32 _485_22 = ((_entry_0 >> 27) & 1);
      u32 _485_23 = ((_entry_0 >> 28) & 1);
      u32 _485_24 = ((_entry_0 >> 29) & 1);
      u32 _485_25 = ((_entry_0 >> 30) & 1);
      u32 _485_26 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_62[1];
      if (spin_51(e, _o_62, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_62[0];
      WL_RETN(1);
    } else if (_entry_0 == 11) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1059;
        WL_PUSHN(1);
      } else {
        u64 _t_74 = task_node(e, FID_ffi_go_k1059, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1059, _t_74);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_workflow_get_req)) {
        u64 _t_75 = task_node(e, FID_ffi_workflow_get_req, WL_CONT, WL_IDX, 0);
        e.mem[_t_75 + 0] = _input_0;
        return term_tsk(FID_ffi_workflow_get_req, _t_75);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_workflow_get_req);
    } else if ((_entry_0 & 15) == 11) {
      u32 _540_0 = ((_entry_0 >> 4) & 1);
      u32 _541_0 = ((_entry_0 >> 5) & 1);
      u32 _541_1 = ((_entry_0 >> 6) & 1);
      u32 _541_2 = ((_entry_0 >> 7) & 1);
      u32 _541_3 = ((_entry_0 >> 8) & 1);
      u32 _541_4 = ((_entry_0 >> 9) & 1);
      u32 _541_5 = ((_entry_0 >> 10) & 1);
      u32 _541_6 = ((_entry_0 >> 11) & 1);
      u32 _541_7 = ((_entry_0 >> 12) & 1);
      u32 _541_8 = ((_entry_0 >> 13) & 1);
      u32 _541_9 = ((_entry_0 >> 14) & 1);
      u32 _541_10 = ((_entry_0 >> 15) & 1);
      u32 _541_11 = ((_entry_0 >> 16) & 1);
      u32 _541_12 = ((_entry_0 >> 17) & 1);
      u32 _541_13 = ((_entry_0 >> 18) & 1);
      u32 _541_14 = ((_entry_0 >> 19) & 1);
      u32 _541_15 = ((_entry_0 >> 20) & 1);
      u32 _541_16 = ((_entry_0 >> 21) & 1);
      u32 _541_17 = ((_entry_0 >> 22) & 1);
      u32 _541_18 = ((_entry_0 >> 23) & 1);
      u32 _541_19 = ((_entry_0 >> 24) & 1);
      u32 _541_20 = ((_entry_0 >> 25) & 1);
      u32 _541_21 = ((_entry_0 >> 26) & 1);
      u32 _541_22 = ((_entry_0 >> 27) & 1);
      u32 _541_23 = ((_entry_0 >> 28) & 1);
      u32 _541_24 = ((_entry_0 >> 29) & 1);
      u32 _541_25 = ((_entry_0 >> 30) & 1);
      u32 _541_26 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_69[1];
      if (spin_51(e, _o_69, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_69[0];
      WL_RETN(1);
    } else if (_entry_0 == 7) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_ffi_go_k1061;
        WL_PUSHN(1);
      } else {
        u64 _t_78 = task_node(e, FID_ffi_go_k1061, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_ffi_go_k1061, _t_78);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_5)) {
        u64 _t_79 = task_node(e, FID_wire_get_list_5, WL_CONT, WL_IDX, 0);
        e.mem[_t_79 + 0] = _input_0;
        return term_tsk(FID_wire_get_list_5, _t_79);
      }
      r0 = _input_0;
      WL_JMP(FID_wire_get_list_5);
    } else {
      u32 _596_0 = ((_entry_0 >> 3) & 1);
      u32 _597_0 = ((_entry_0 >> 4) & 1);
      u32 _597_1 = ((_entry_0 >> 5) & 1);
      u32 _597_2 = ((_entry_0 >> 6) & 1);
      u32 _597_3 = ((_entry_0 >> 7) & 1);
      u32 _597_4 = ((_entry_0 >> 8) & 1);
      u32 _597_5 = ((_entry_0 >> 9) & 1);
      u32 _597_6 = ((_entry_0 >> 10) & 1);
      u32 _597_7 = ((_entry_0 >> 11) & 1);
      u32 _597_8 = ((_entry_0 >> 12) & 1);
      u32 _597_9 = ((_entry_0 >> 13) & 1);
      u32 _597_10 = ((_entry_0 >> 14) & 1);
      u32 _597_11 = ((_entry_0 >> 15) & 1);
      u32 _597_12 = ((_entry_0 >> 16) & 1);
      u32 _597_13 = ((_entry_0 >> 17) & 1);
      u32 _597_14 = ((_entry_0 >> 18) & 1);
      u32 _597_15 = ((_entry_0 >> 19) & 1);
      u32 _597_16 = ((_entry_0 >> 20) & 1);
      u32 _597_17 = ((_entry_0 >> 21) & 1);
      u32 _597_18 = ((_entry_0 >> 22) & 1);
      u32 _597_19 = ((_entry_0 >> 23) & 1);
      u32 _597_20 = ((_entry_0 >> 24) & 1);
      u32 _597_21 = ((_entry_0 >> 25) & 1);
      u32 _597_22 = ((_entry_0 >> 26) & 1);
      u32 _597_23 = ((_entry_0 >> 27) & 1);
      u32 _597_24 = ((_entry_0 >> 28) & 1);
      u32 _597_25 = ((_entry_0 >> 29) & 1);
      u32 _597_26 = ((_entry_0 >> 30) & 1);
      u32 _597_27 = ((_entry_0 >> 31) & 1);
      term_sink(e, _input_0);
      Term _o_75[1];
      if (spin_51(e, _o_75, term_ctr(CID_SCon, STAT_OFF + 1494)) == 0) {
        return 0;
      }
      r0 = _o_75[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1022)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    WL_OPEN
    if (_h_0 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_1;
        STK(1) = FID_ffi_go_k1023;
        WL_PUSHN(2);
      } else {
        u64 _t_2 = task_node(e, FID_ffi_go_k1023, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _h_1;
        WL_CONT = term_tsk(FID_ffi_go_k1023, _t_2);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_job_get_cap)) {
        u64 _t_3 = task_node(e, FID_ffi_job_get_cap, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _h_2;
        return term_tsk(FID_ffi_job_get_cap, _t_3);
      }
      r0 = _h_2;
      WL_JMP(FID_ffi_job_get_cap);
    } else {
      Term _o_10[1];
      if (spin_51(e, _o_10, term_ctr(CID_SCon, STAT_OFF + 1276)) == 0) {
        return 0;
      }
      r0 = _o_10[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1023)
    WL_POPN(1);
    Term _h_7 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    WL_OPEN
    if (_h_3 == 0) {
      if (seq) {
        WL_ROOM(4, 0);
        STK(0) = _h_7;
        STK(1) = _h_4;
        STK(2) = _h_5;
        STK(3) = FID_ffi_go_k1024;
        WL_PUSHN(4);
      } else {
        u64 _t_4 = task_node(e, FID_ffi_go_k1024, WL_CONT, WL_IDX, 1);
        e.mem[_t_4 + 0] = _h_7;
        e.mem[_t_4 + 1] = _h_4;
        e.mem[_t_4 + 2] = _h_5;
        WL_CONT = term_tsk(FID_ffi_go_k1024, _t_4);
        WL_IDX = 3;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_job_get_job)) {
        u64 _t_5 = task_node(e, FID_ffi_job_get_job, WL_CONT, WL_IDX, 0);
        e.mem[_t_5 + 0] = _h_6;
        return term_tsk(FID_ffi_job_get_job, _t_5);
      }
      r0 = _h_6;
      WL_JMP(FID_ffi_job_get_job);
    } else {
      Term _o_9[1];
      if (spin_51(e, _o_9, term_ctr(CID_SCon, STAT_OFF + 946)) == 0) {
        return 0;
      }
      r0 = _o_9[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1024)
    WL_POPN(3);
    Term _h_16 = STK(0);
    u32 _h_17 = STK(1);
    Term _h_18 = STK(2);
    u32 _h_8 = r0;
    u32 _h_9 = r1;
    Term _h_10 = r2;
    Term _h_11 = r3;
    u32 _h_12 = r4;
    u32 _h_13 = r5;
    u32 _h_14 = r6;
    Term _h_15 = r7;
    WL_OPEN
    if (_h_8 == 0) {
      if (seq) {
        WL_ROOM(10, 0);
        STK(0) = _h_16;
        STK(1) = _h_17;
        STK(2) = _h_18;
        STK(3) = _h_9;
        STK(4) = _h_10;
        STK(5) = _h_11;
        STK(6) = _h_12;
        STK(7) = _h_13;
        STK(8) = _h_14;
        STK(9) = FID_ffi_go_k1025;
        WL_PUSHN(10);
      } else {
        u64 _t_6 = task_node(e, FID_ffi_go_k1025, WL_CONT, WL_IDX, 1);
        e.mem[_t_6 + 0] = _h_16;
        e.mem[_t_6 + 1] = _h_17;
        e.mem[_t_6 + 2] = _h_18;
        e.mem[_t_6 + 3] = _h_9;
        e.mem[_t_6 + 4] = _h_10;
        e.mem[_t_6 + 5] = _h_11;
        e.mem[_t_6 + 6] = _h_12;
        e.mem[_t_6 + 7] = _h_13;
        e.mem[_t_6 + 8] = _h_14;
        WL_CONT = term_tsk(FID_ffi_go_k1025, _t_6);
        WL_IDX = 9;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_job_get_ev)) {
        u64 _t_7 = task_node(e, FID_ffi_job_get_ev, WL_CONT, WL_IDX, 0);
        e.mem[_t_7 + 0] = _h_15;
        return term_tsk(FID_ffi_job_get_ev, _t_7);
      }
      r0 = _h_15;
      WL_JMP(FID_ffi_job_get_ev);
    } else {
      Term _o_8[1];
      if (spin_51(e, _o_8, term_ctr(CID_SCon, STAT_OFF + 652)) == 0) {
        return 0;
      }
      r0 = _o_8[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1025)
    WL_POPN(9);
    Term _h_24 = STK(0);
    u32 _h_25 = STK(1);
    Term _h_26 = STK(2);
    u32 _h_27 = STK(3);
    Term _h_28 = STK(4);
    Term _h_29 = STK(5);
    u32 _h_30 = STK(6);
    u32 _h_31 = STK(7);
    u32 _h_32 = STK(8);
    u32 _h_19 = r0;
    u32 _h_20 = r1;
    Term _h_21 = r2;
    u32 _h_22 = r3;
    Term _h_23 = r4;
    WL_OPEN
    if (_h_19 == 0) {
      u32 _v_0 = 0;
      Term _o_2[1];
      if (spin_77(e, _o_2, _h_23) == 0) {
        return 0;
      }
      _v_0 = (u32)_o_2[0];
      if (_v_0 == 1) {
        u32 _v_1 = 0;
        Term _v_2 = 0;
        Term _v_3 = 0;
        u32 _v_4 = 0;
        u32 _v_5 = 0;
        u32 _v_6 = 0;
        Term _o_3[6];
        if (spin_159(e, _o_3, _h_24, _h_25, _h_26, _h_27, _h_28, _h_29, _h_30, _h_31, _h_32, _h_20, _h_21, _h_22) == 0) {
          return 0;
        }
        _v_1 = (u32)_o_3[0];
        _v_2 = _o_3[1];
        _v_3 = _o_3[2];
        _v_4 = (u32)_o_3[3];
        _v_5 = (u32)_o_3[4];
        _v_6 = (u32)_o_3[5];
        Term _v_7 = 0;
        Term _o_4[1];
        if (spin_160(e, _o_4, _h_27, _h_28, _h_29, _h_30, _h_31, _h_32, _h_20, _h_21, _h_22) == 0) {
          return 0;
        }
        _v_7 = _o_4[0];
        if (seq) {
          WL_ROOM(7, 0);
          STK(0) = _v_1;
          STK(1) = _v_2;
          STK(2) = _v_3;
          STK(3) = _v_4;
          STK(4) = _v_5;
          STK(5) = _v_6;
          STK(6) = FID_ffi_go_k1026;
          WL_PUSHN(7);
        } else {
          u64 _t_8 = task_node(e, FID_ffi_go_k1026, WL_CONT, WL_IDX, 1);
          e.mem[_t_8 + 0] = _v_1;
          e.mem[_t_8 + 1] = _v_2;
          e.mem[_t_8 + 2] = _v_3;
          e.mem[_t_8 + 3] = _v_4;
          e.mem[_t_8 + 4] = _v_5;
          e.mem[_t_8 + 5] = _v_6;
          WL_CONT = term_tsk(FID_ffi_go_k1026, _t_8);
          WL_IDX = 6;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_9)) {
          u64 _t_9 = task_node(e, FID_wire_put_list_9, WL_CONT, WL_IDX, 0);
          e.mem[_t_9 + 0] = _v_7;
          e.mem[_t_9 + 1] = term_pak(CID_SNil, 0);
          return term_tsk(FID_wire_put_list_9, _t_9);
        }
        r0 = _v_7;
        r1 = term_pak(CID_SNil, 0);
        WL_JMP(FID_wire_put_list_9);
      } else {
        Term _o_6[1];
        if (spin_51(e, _o_6, term_ctr(CID_SCon, STAT_OFF + 212)) == 0) {
          return 0;
        }
        r0 = _o_6[0];
        WL_RETN(1);
      }
    } else {
      Term _o_7[1];
      if (spin_51(e, _o_7, term_ctr(CID_SCon, STAT_OFF + 408)) == 0) {
        return 0;
      }
      r0 = _o_7[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1026)
    WL_POPN(6);
    u32 _v_8 = STK(0);
    Term _v_9 = STK(1);
    Term _v_10 = STK(2);
    u32 _v_11 = STK(3);
    u32 _v_12 = STK(4);
    u32 _v_13 = STK(5);
    Term _h_33 = r0;
    WL_OPEN
    Term _o_5[1];
    if (spin_120(e, _o_5, _v_8, _v_9, _v_10, _v_11, _v_12, _v_13, _h_33) == 0) {
      return 0;
    }
    r0 = _o_5[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1027)
    u32 _h_34 = r0;
    Term _h_35 = r1;
    Term _h_36 = r2;
    WL_OPEN
    if (_h_34 == 0) {
      u32 _v_14 = 0;
      Term _o_12[1];
      if (spin_47(e, _o_12, _h_35) == 0) {
        return 0;
      }
      _v_14 = (u32)_o_12[0];
      if (_v_14 == 0) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k1028;
          WL_PUSHN(1);
        } else {
          u64 _t_12 = task_node(e, FID_ffi_go_k1028, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k1028, _t_12);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_cfg)) {
          u64 _t_13 = task_node(e, FID_ffi_child_get_cfg, WL_CONT, WL_IDX, 0);
          e.mem[_t_13 + 0] = _h_36;
          return term_tsk(FID_ffi_child_get_cfg, _t_13);
        }
        r0 = _h_36;
        WL_JMP(FID_ffi_child_get_cfg);
      } else if (_v_14 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k1033;
          WL_PUSHN(1);
        } else {
          u64 _t_22 = task_node(e, FID_ffi_go_k1033, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k1033, _t_22);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_mfate)) {
          u64 _t_23 = task_node(e, FID_ffi_child_get_mfate, WL_CONT, WL_IDX, 0);
          e.mem[_t_23 + 0] = _h_36;
          return term_tsk(FID_ffi_child_get_mfate, _t_23);
        }
        r0 = _h_36;
        WL_JMP(FID_ffi_child_get_mfate);
      } else if (_v_14 == 2) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k1035;
          WL_PUSHN(1);
        } else {
          u64 _t_26 = task_node(e, FID_ffi_go_k1035, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k1035, _t_26);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_ph)) {
          u64 _t_27 = task_node(e, FID_ffi_child_get_ph, WL_CONT, WL_IDX, 0);
          e.mem[_t_27 + 0] = _h_36;
          return term_tsk(FID_ffi_child_get_ph, _t_27);
        }
        r0 = _h_36;
        WL_JMP(FID_ffi_child_get_ph);
      } else if (_v_14 == 3) {
        term_sink(e, _h_36);
        Term _o_21[1];
        if (spin_51(e, _o_21, term_ctr(CID_SCon, STAT_OFF + 940)) == 0) {
          return 0;
        }
        r0 = _o_21[0];
        WL_RETN(1);
      } else if (_v_14 == 4) {
        term_sink(e, _h_36);
        Term _o_22[1];
        if (spin_51(e, _o_22, term_ctr(CID_SCon, STAT_OFF + 940)) == 0) {
          return 0;
        }
        r0 = _o_22[0];
        WL_RETN(1);
      } else {
        term_sink(e, _h_36);
        Term _o_23[1];
        if (spin_51(e, _o_23, term_ctr(CID_SCon, STAT_OFF + 940)) == 0) {
          return 0;
        }
        r0 = _o_23[0];
        WL_RETN(1);
      }
    } else {
      Term _o_24[1];
      if (spin_51(e, _o_24, term_ctr(CID_SCon, STAT_OFF + 1270)) == 0) {
        return 0;
      }
      r0 = _o_24[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1028)
    u32 _h_37 = r0;
    Term _h_38 = r1;
    Term _h_39 = r2;
    Term _h_40 = r3;
    WL_OPEN
    if (_h_37 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_38;
        STK(1) = _h_39;
        STK(2) = FID_ffi_go_k1029;
        WL_PUSHN(3);
      } else {
        u64 _t_14 = task_node(e, FID_ffi_go_k1029, WL_CONT, WL_IDX, 1);
        e.mem[_t_14 + 0] = _h_38;
        e.mem[_t_14 + 1] = _h_39;
        WL_CONT = term_tsk(FID_ffi_go_k1029, _t_14);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_w)) {
        u64 _t_15 = task_node(e, FID_ffi_child_get_w, WL_CONT, WL_IDX, 0);
        e.mem[_t_15 + 0] = _h_40;
        return term_tsk(FID_ffi_child_get_w, _t_15);
      }
      r0 = _h_40;
      WL_JMP(FID_ffi_child_get_w);
    } else {
      Term _o_17[1];
      if (spin_51(e, _o_17, term_ctr(CID_SCon, STAT_OFF + 626)) == 0) {
        return 0;
      }
      r0 = _o_17[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1029)
    WL_POPN(2);
    Term _h_47 = STK(0);
    Term _h_48 = STK(1);
    u32 _h_41 = r0;
    u32 _h_42 = r1;
    Term _h_43 = r2;
    Term _h_44 = r3;
    Term _h_45 = r4;
    Term _h_46 = r5;
    WL_OPEN
    if (_h_41 == 0) {
      if (seq) {
        WL_ROOM(7, 0);
        STK(0) = _h_47;
        STK(1) = _h_48;
        STK(2) = _h_42;
        STK(3) = _h_43;
        STK(4) = _h_44;
        STK(5) = _h_45;
        STK(6) = FID_ffi_go_k1030;
        WL_PUSHN(7);
      } else {
        u64 _t_16 = task_node(e, FID_ffi_go_k1030, WL_CONT, WL_IDX, 1);
        e.mem[_t_16 + 0] = _h_47;
        e.mem[_t_16 + 1] = _h_48;
        e.mem[_t_16 + 2] = _h_42;
        e.mem[_t_16 + 3] = _h_43;
        e.mem[_t_16 + 4] = _h_44;
        e.mem[_t_16 + 5] = _h_45;
        WL_CONT = term_tsk(FID_ffi_go_k1030, _t_16);
        WL_IDX = 6;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_17 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_17 + 0] = _h_46;
        return term_tsk(FID_wire_get_nat, _t_17);
      }
      r0 = _h_46;
      WL_JMP(FID_wire_get_nat);
    } else {
      Term _o_16[1];
      if (spin_51(e, _o_16, term_ctr(CID_SCon, STAT_OFF + 362)) == 0) {
        return 0;
      }
      r0 = _o_16[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1030)
    WL_POPN(6);
    Term _h_52 = STK(0);
    Term _h_53 = STK(1);
    u32 _h_54 = STK(2);
    Term _h_55 = STK(3);
    Term _h_56 = STK(4);
    Term _h_57 = STK(5);
    u32 _h_49 = r0;
    Term _h_50 = r1;
    Term _h_51 = r2;
    WL_OPEN
    if (_h_49 == 0) {
      if (seq) {
        WL_ROOM(8, 0);
        STK(0) = _h_52;
        STK(1) = _h_53;
        STK(2) = _h_54;
        STK(3) = _h_55;
        STK(4) = _h_56;
        STK(5) = _h_57;
        STK(6) = _h_50;
        STK(7) = FID_ffi_go_k1031;
        WL_PUSHN(8);
      } else {
        u64 _t_18 = task_node(e, FID_ffi_go_k1031, WL_CONT, WL_IDX, 1);
        e.mem[_t_18 + 0] = _h_52;
        e.mem[_t_18 + 1] = _h_53;
        e.mem[_t_18 + 2] = _h_54;
        e.mem[_t_18 + 3] = _h_55;
        e.mem[_t_18 + 4] = _h_56;
        e.mem[_t_18 + 5] = _h_57;
        e.mem[_t_18 + 6] = _h_50;
        WL_CONT = term_tsk(FID_ffi_go_k1031, _t_18);
        WL_IDX = 7;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_obs)) {
        u64 _t_19 = task_node(e, FID_ffi_child_get_obs, WL_CONT, WL_IDX, 0);
        e.mem[_t_19 + 0] = _h_51;
        return term_tsk(FID_ffi_child_get_obs, _t_19);
      }
      r0 = _h_51;
      WL_JMP(FID_ffi_child_get_obs);
    } else {
      Term _o_15[1];
      if (spin_51(e, _o_15, term_ctr(CID_SCon, STAT_OFF + 206)) == 0) {
        return 0;
      }
      r0 = _o_15[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1031)
    WL_POPN(7);
    Term _h_63 = STK(0);
    Term _h_64 = STK(1);
    u32 _h_65 = STK(2);
    Term _h_66 = STK(3);
    Term _h_67 = STK(4);
    Term _h_68 = STK(5);
    Term _h_69 = STK(6);
    u32 _h_58 = r0;
    u32 _h_59 = r1;
    u32 _h_60 = r2;
    Term _h_61 = r3;
    Term _h_62 = r4;
    WL_OPEN
    if (_h_58 == 0) {
      if (seq) {
        WL_ROOM(11, 0);
        STK(0) = _h_63;
        STK(1) = _h_64;
        STK(2) = _h_65;
        STK(3) = _h_66;
        STK(4) = _h_67;
        STK(5) = _h_68;
        STK(6) = _h_69;
        STK(7) = _h_59;
        STK(8) = _h_60;
        STK(9) = _h_61;
        STK(10) = FID_ffi_go_k1032;
        WL_PUSHN(11);
      } else {
        u64 _t_20 = task_node(e, FID_ffi_go_k1032, WL_CONT, WL_IDX, 1);
        e.mem[_t_20 + 0] = _h_63;
        e.mem[_t_20 + 1] = _h_64;
        e.mem[_t_20 + 2] = _h_65;
        e.mem[_t_20 + 3] = _h_66;
        e.mem[_t_20 + 4] = _h_67;
        e.mem[_t_20 + 5] = _h_68;
        e.mem[_t_20 + 6] = _h_69;
        e.mem[_t_20 + 7] = _h_59;
        e.mem[_t_20 + 8] = _h_60;
        e.mem[_t_20 + 9] = _h_61;
        WL_CONT = term_tsk(FID_ffi_go_k1032, _t_20);
        WL_IDX = 10;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_child_get_mode)) {
        u64 _t_21 = task_node(e, FID_ffi_child_get_mode, WL_CONT, WL_IDX, 0);
        e.mem[_t_21 + 0] = _h_62;
        return term_tsk(FID_ffi_child_get_mode, _t_21);
      }
      r0 = _h_62;
      WL_JMP(FID_ffi_child_get_mode);
    } else {
      Term _o_14[1];
      if (spin_51(e, _o_14, term_ctr(CID_SCon, STAT_OFF + 102)) == 0) {
        return 0;
      }
      r0 = _o_14[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1032)
    WL_POPN(10);
    Term _h_73 = STK(0);
    Term _h_74 = STK(1);
    u32 _h_75 = STK(2);
    Term _h_76 = STK(3);
    Term _h_77 = STK(4);
    Term _h_78 = STK(5);
    Term _h_79 = STK(6);
    u32 _h_80 = STK(7);
    u32 _h_81 = STK(8);
    Term _h_82 = STK(9);
    u32 _h_70 = r0;
    u32 _h_71 = r1;
    Term _h_72 = r2;
    WL_OPEN
    Term _o_13[1];
    if (spin_114(e, _o_13, _h_73, _h_74, _h_75, _h_76, _h_77, _h_78, _h_79, _h_80, _h_81, _h_82, _h_70, _h_71, _h_72) == 0) {
      return 0;
    }
    r0 = _o_13[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1033)
    u32 _h_83 = r0;
    u32 _h_84 = r1;
    u32 _h_85 = r2;
    Term _h_86 = r3;
    WL_OPEN
    if (_h_83 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_84;
        STK(1) = _h_85;
        STK(2) = FID_ffi_go_k1034;
        WL_PUSHN(3);
      } else {
        u64 _t_24 = task_node(e, FID_ffi_go_k1034, WL_CONT, WL_IDX, 1);
        e.mem[_t_24 + 0] = _h_84;
        e.mem[_t_24 + 1] = _h_85;
        WL_CONT = term_tsk(FID_ffi_go_k1034, _t_24);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_25 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_25 + 0] = _h_86;
        return term_tsk(FID_wire_get_nat, _t_25);
      }
      r0 = _h_86;
      WL_JMP(FID_wire_get_nat);
    } else {
      Term _o_19[1];
      if (spin_51(e, _o_19, term_ctr(CID_SCon, STAT_OFF + 590)) == 0) {
        return 0;
      }
      r0 = _o_19[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1034)
    WL_POPN(2);
    u32 _h_90 = STK(0);
    u32 _h_91 = STK(1);
    u32 _h_87 = r0;
    Term _h_88 = r1;
    Term _h_89 = r2;
    WL_OPEN
    Term _o_18[1];
    if (spin_218(e, _o_18, _h_90, _h_91, _h_87, _h_88, _h_89) == 0) {
      return 0;
    }
    r0 = _o_18[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1035)
    u32 _h_92 = r0;
    u32 _h_93 = r1;
    u32 _h_94 = r2;
    Term _h_95 = r3;
    Term _h_96 = r4;
    Term _h_97 = r5;
    Term _h_98 = r6;
    WL_OPEN
    Term _o_20[1];
    if (spin_226(e, _o_20, _h_92, _h_93, _h_94, _h_95, _h_96, _h_97, _h_98) == 0) {
      return 0;
    }
    r0 = _o_20[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1036)
    u32 _h_99 = r0;
    Term _h_100 = r1;
    Term _h_101 = r2;
    WL_OPEN
    if (_h_99 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_100;
        STK(1) = FID_ffi_go_k1037;
        WL_PUSHN(2);
      } else {
        u64 _t_30 = task_node(e, FID_ffi_go_k1037, WL_CONT, WL_IDX, 1);
        e.mem[_t_30 + 0] = _h_100;
        WL_CONT = term_tsk(FID_ffi_go_k1037, _t_30);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_doc_lines_get_end)) {
        u64 _t_31 = task_node(e, FID_ffi_doc_lines_get_end, WL_CONT, WL_IDX, 0);
        e.mem[_t_31 + 0] = _h_101;
        return term_tsk(FID_ffi_doc_lines_get_end, _t_31);
      }
      r0 = _h_101;
      WL_JMP(FID_ffi_doc_lines_get_end);
    } else {
      Term _o_30[1];
      if (spin_51(e, _o_30, term_ctr(CID_SCon, STAT_OFF + 1252)) == 0) {
        return 0;
      }
      r0 = _o_30[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1037)
    WL_POPN(1);
    Term _h_105 = STK(0);
    u32 _h_102 = r0;
    u32 _h_103 = r1;
    Term _h_104 = r2;
    WL_OPEN
    if (_h_102 == 0) {
      u32 _v_15 = 0;
      Term _o_26[1];
      if (spin_77(e, _o_26, _h_104) == 0) {
        return 0;
      }
      _v_15 = (u32)_o_26[0];
      if (_v_15 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k1038;
          WL_PUSHN(1);
        } else {
          u64 _t_32 = task_node(e, FID_ffi_go_k1038, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k1038, _t_32);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_doc_lines_plan)) {
          u64 _t_33 = task_node(e, FID_doc_lines_plan, WL_CONT, WL_IDX, 0);
          e.mem[_t_33 + 0] = _h_105;
          e.mem[_t_33 + 1] = _h_103;
          return term_tsk(FID_doc_lines_plan, _t_33);
        }
        r0 = _h_105;
        r1 = _h_103;
        WL_JMP(FID_doc_lines_plan);
      } else {
        term_sink(e, _h_105);
        Term _o_28[1];
        if (spin_51(e, _o_28, term_ctr(CID_SCon, STAT_OFF + 532)) == 0) {
          return 0;
        }
        r0 = _o_28[0];
        WL_RETN(1);
      }
    } else {
      term_sink(e, _h_105);
      Term _o_29[1];
      if (spin_51(e, _o_29, term_ctr(CID_SCon, STAT_OFF + 912)) == 0) {
        return 0;
      }
      r0 = _o_29[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1038)
    Term _h_106 = r0;
    WL_OPEN
    Term _rest_0 = term_pak(CID_SNil, 0);
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_go_k1039;
      WL_PUSHN(1);
    } else {
      u64 _t_34 = task_node(e, FID_ffi_go_k1039, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_go_k1039, _t_34);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_4)) {
      u64 _t_35 = task_node(e, FID_wire_put_list_go_4, WL_CONT, WL_IDX, 0);
      e.mem[_t_35 + 0] = _h_106;
      e.mem[_t_35 + 1] = _rest_0;
      return term_tsk(FID_wire_put_list_go_4, _t_35);
    }
    r0 = _h_106;
    r1 = _rest_0;
    WL_JMP(FID_wire_put_list_go_4);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1039)
    Term _h_107 = r0;
    Term _h_108 = r1;
    WL_OPEN
    Term _o_27[1];
    if (spin_82(e, _o_27, _h_107, _h_108) == 0) {
      return 0;
    }
    r0 = _o_27[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1040)
    u32 _h_109 = r0;
    u32 _h_110 = r1;
    Term _h_111 = r2;
    Term _h_112 = r3;
    WL_OPEN
    if (_h_109 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_110;
        STK(1) = _h_111;
        STK(2) = FID_ffi_go_k1041;
        WL_PUSHN(3);
      } else {
        u64 _t_38 = task_node(e, FID_ffi_go_k1041, WL_CONT, WL_IDX, 1);
        e.mem[_t_38 + 0] = _h_110;
        e.mem[_t_38 + 1] = _h_111;
        WL_CONT = term_tsk(FID_ffi_go_k1041, _t_38);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_sandbox_get_doc)) {
        u64 _t_39 = task_node(e, FID_ffi_sandbox_get_doc, WL_CONT, WL_IDX, 0);
        e.mem[_t_39 + 0] = _h_112;
        return term_tsk(FID_ffi_sandbox_get_doc, _t_39);
      }
      r0 = _h_112;
      WL_JMP(FID_ffi_sandbox_get_doc);
    } else {
      Term _o_34[1];
      if (spin_51(e, _o_34, term_ctr(CID_SCon, STAT_OFF + 1212)) == 0) {
        return 0;
      }
      r0 = _o_34[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1041)
    WL_POPN(2);
    u32 _h_117 = STK(0);
    Term _h_118 = STK(1);
    u32 _h_113 = r0;
    u32 _h_114 = r1;
    Term _h_115 = r2;
    Term _h_116 = r3;
    WL_OPEN
    if (_h_113 == 0) {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _h_117;
        STK(1) = _h_118;
        STK(2) = _h_114;
        STK(3) = _h_115;
        STK(4) = FID_ffi_go_k1042;
        WL_PUSHN(5);
      } else {
        u64 _t_40 = task_node(e, FID_ffi_go_k1042, WL_CONT, WL_IDX, 1);
        e.mem[_t_40 + 0] = _h_117;
        e.mem[_t_40 + 1] = _h_118;
        e.mem[_t_40 + 2] = _h_114;
        e.mem[_t_40 + 3] = _h_115;
        WL_CONT = term_tsk(FID_ffi_go_k1042, _t_40);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_sandbox_get_doc)) {
        u64 _t_41 = task_node(e, FID_ffi_sandbox_get_doc, WL_CONT, WL_IDX, 0);
        e.mem[_t_41 + 0] = _h_116;
        return term_tsk(FID_ffi_sandbox_get_doc, _t_41);
      }
      r0 = _h_116;
      WL_JMP(FID_ffi_sandbox_get_doc);
    } else {
      Term _o_33[1];
      if (spin_51(e, _o_33, term_ctr(CID_SCon, STAT_OFF + 860)) == 0) {
        return 0;
      }
      r0 = _o_33[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1042)
    WL_POPN(4);
    u32 _h_123 = STK(0);
    Term _h_124 = STK(1);
    u32 _h_125 = STK(2);
    Term _h_126 = STK(3);
    u32 _h_119 = r0;
    u32 _h_120 = r1;
    Term _h_121 = r2;
    Term _h_122 = r3;
    WL_OPEN
    Term _o_32[1];
    if (spin_224(e, _o_32, _h_123, _h_124, _h_125, _h_126, _h_119, _h_120, _h_121, _h_122) == 0) {
      return 0;
    }
    r0 = _o_32[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1043)
    u32 _h_127 = r0;
    Term _h_128 = r1;
    Term _h_129 = r2;
    WL_OPEN
    if (_h_127 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_128;
        STK(1) = FID_ffi_go_k1044;
        WL_PUSHN(2);
      } else {
        u64 _t_44 = task_node(e, FID_ffi_go_k1044, WL_CONT, WL_IDX, 1);
        e.mem[_t_44 + 0] = _h_128;
        WL_CONT = term_tsk(FID_ffi_go_k1044, _t_44);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_u32)) {
        u64 _t_45 = task_node(e, FID_wire_get_u32, WL_CONT, WL_IDX, 0);
        e.mem[_t_45 + 0] = _h_129;
        return term_tsk(FID_wire_get_u32, _t_45);
      }
      r0 = _h_129;
      WL_JMP(FID_wire_get_u32);
    } else {
      Term _o_45[1];
      if (spin_148(e, _o_45) == 0) {
        return 0;
      }
      r0 = _o_45[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1044)
    WL_POPN(1);
    Term _h_133 = STK(0);
    u32 _h_130 = r0;
    u32 _h_131 = r1;
    Term _h_132 = r2;
    WL_OPEN
    if (_h_130 == 0) {
      u32 _v_16 = 0;
      u32 _v_17 = 0;
      Term _v_18 = 0;
      Term _o_36[3];
      if (spin_43(e, _o_36, _h_132) == 0) {
        return 0;
      }
      _v_16 = (u32)_o_36[0];
      _v_17 = (u32)_o_36[1];
      _v_18 = _o_36[2];
      if (_v_16 == 0) {
        if (seq) {
          WL_ROOM(4, 0);
          STK(0) = _v_17;
          STK(1) = _h_133;
          STK(2) = _h_131;
          STK(3) = FID_ffi_go_k1045;
          WL_PUSHN(4);
        } else {
          u64 _t_46 = task_node(e, FID_ffi_go_k1045, WL_CONT, WL_IDX, 1);
          e.mem[_t_46 + 0] = _v_17;
          e.mem[_t_46 + 1] = _h_133;
          e.mem[_t_46 + 2] = _h_131;
          WL_CONT = term_tsk(FID_ffi_go_k1045, _t_46);
          WL_IDX = 3;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_get_str)) {
          u64 _t_47 = task_node(e, FID_wire_get_str, WL_CONT, WL_IDX, 0);
          e.mem[_t_47 + 0] = _v_18;
          return term_tsk(FID_wire_get_str, _t_47);
        }
        r0 = _v_18;
        WL_JMP(FID_wire_get_str);
      } else {
        Term _o_43[1];
        if (spin_148(e, _o_43) == 0) {
          return 0;
        }
        r0 = _o_43[0];
        WL_RETN(1);
      }
    } else {
      Term _o_44[1];
      if (spin_148(e, _o_44) == 0) {
        return 0;
      }
      r0 = _o_44[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1045)
    WL_POPN(3);
    u32 _v_19 = STK(0);
    Term _h_137 = STK(1);
    u32 _h_138 = STK(2);
    u32 _h_134 = r0;
    Term _h_135 = r1;
    Term _h_136 = r2;
    WL_OPEN
    if (_h_134 == 0) {
      if (seq) {
        WL_ROOM(5, 0);
        STK(0) = _h_135;
        STK(1) = _h_137;
        STK(2) = _h_138;
        STK(3) = _v_19;
        STK(4) = FID_ffi_go_k1046;
        WL_PUSHN(5);
      } else {
        u64 _t_48 = task_node(e, FID_ffi_go_k1046, WL_CONT, WL_IDX, 1);
        e.mem[_t_48 + 0] = _h_135;
        e.mem[_t_48 + 1] = _h_137;
        e.mem[_t_48 + 2] = _h_138;
        e.mem[_t_48 + 3] = _v_19;
        WL_CONT = term_tsk(FID_ffi_go_k1046, _t_48);
        WL_IDX = 4;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_6)) {
        u64 _t_49 = task_node(e, FID_wire_get_list_6, WL_CONT, WL_IDX, 0);
        e.mem[_t_49 + 0] = _h_136;
        return term_tsk(FID_wire_get_list_6, _t_49);
      }
      r0 = _h_136;
      WL_JMP(FID_wire_get_list_6);
    } else {
      Term _o_42[1];
      if (spin_148(e, _o_42) == 0) {
        return 0;
      }
      r0 = _o_42[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1046)
    WL_POPN(4);
    Term _h_142 = STK(0);
    Term _h_143 = STK(1);
    u32 _h_144 = STK(2);
    u32 _v_20 = STK(3);
    u32 _h_139 = r0;
    Term _h_140 = r1;
    Term _h_141 = r2;
    WL_OPEN
    if (_h_139 == 0) {
      if (term_aux(_h_141) == CID_SNil) {
        if (seq) {
          WL_ROOM(5, 0);
          STK(0) = _h_143;
          STK(1) = _h_144;
          STK(2) = _v_20;
          STK(3) = _h_142;
          STK(4) = FID_ffi_go_k1047;
          WL_PUSHN(5);
        } else {
          u64 _t_50 = task_node(e, FID_ffi_go_k1047, WL_CONT, WL_IDX, 1);
          e.mem[_t_50 + 0] = _h_143;
          e.mem[_t_50 + 1] = _h_144;
          e.mem[_t_50 + 2] = _v_20;
          e.mem[_t_50 + 3] = _h_142;
          WL_CONT = term_tsk(FID_ffi_go_k1047, _t_50);
          WL_IDX = 4;
        }
        if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_5)) {
          u64 _t_51 = task_node(e, FID_wire_put_list_5, WL_CONT, WL_IDX, 0);
          e.mem[_t_51 + 0] = _h_140;
          e.mem[_t_51 + 1] = term_pak(CID_SNil, 0);
          return term_tsk(FID_wire_put_list_5, _t_51);
        }
        r0 = _h_140;
        r1 = term_pak(CID_SNil, 0);
        WL_JMP(FID_wire_put_list_5);
      } else {
        term_sink(e, _h_140);
        Term _fb_0[2];
        u64 _sp_0 = ctr_take(e, _h_141, 2, _fb_0);
        u32 _f_0 = _fb_0[0];
        Term _f_1 = _fb_0[1];
        term_sink(e, _f_1);
        term_sink(e, _h_142);
        Term _o_40[1];
        if (spin_148(e, _o_40) == 0) {
          return 0;
        }
        spare_free(e, cls_fit(2), _sp_0);
        r0 = _o_40[0];
        WL_RETN(1);
      }
    } else {
      term_sink(e, _h_142);
      Term _o_41[1];
      if (spin_148(e, _o_41) == 0) {
        return 0;
      }
      r0 = _o_41[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1047)
    WL_POPN(4);
    Term _h_146 = STK(0);
    u32 _h_147 = STK(1);
    u32 _v_21 = STK(2);
    Term _h_148 = STK(3);
    Term _h_145 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(4, 0);
      STK(0) = _h_146;
      STK(1) = _h_147;
      STK(2) = _v_21;
      STK(3) = FID_ffi_go_k1048;
      WL_PUSHN(4);
    } else {
      u64 _t_52 = task_node(e, FID_ffi_go_k1048, WL_CONT, WL_IDX, 1);
      e.mem[_t_52 + 0] = _h_146;
      e.mem[_t_52 + 1] = _h_147;
      e.mem[_t_52 + 2] = _v_21;
      WL_CONT = term_tsk(FID_ffi_go_k1048, _t_52);
      WL_IDX = 3;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_str)) {
      u64 _t_53 = task_node(e, FID_wire_put_str, WL_CONT, WL_IDX, 0);
      e.mem[_t_53 + 0] = _h_148;
      e.mem[_t_53 + 1] = _h_145;
      return term_tsk(FID_wire_put_str, _t_53);
    }
    r0 = _h_148;
    r1 = _h_145;
    WL_JMP(FID_wire_put_str);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1048)
    WL_POPN(3);
    Term _h_150 = STK(0);
    u32 _h_151 = STK(1);
    u32 _v_22 = STK(2);
    Term _h_149 = r0;
    WL_OPEN
    Term _v_23 = 0;
    Term _v_24 = 0;
    Term _o_37[1];
    if (spin_147(e, _o_37, _v_22, _h_149) == 0) {
      return 0;
    }
    _v_24 = _o_37[0];
    Term _o_38[1];
    if (spin_31(e, _o_38, _h_151, _v_24) == 0) {
      return 0;
    }
    _v_23 = _o_38[0];
    Term _o_39[1];
    if (spin_15(e, _o_39, _h_150, _v_23) == 0) {
      return 0;
    }
    r0 = _o_39[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1049)
    u32 _h_152 = r0;
    Term _h_153 = r1;
    Term _h_154 = r2;
    WL_OPEN
    if (_h_152 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_153;
        STK(1) = FID_ffi_go_k1050;
        WL_PUSHN(2);
      } else {
        u64 _t_56 = task_node(e, FID_ffi_go_k1050, WL_CONT, WL_IDX, 1);
        e.mem[_t_56 + 0] = _h_153;
        WL_CONT = term_tsk(FID_ffi_go_k1050, _t_56);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_57 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_57 + 0] = _h_154;
        return term_tsk(FID_wire_get_nat, _t_57);
      }
      r0 = _h_154;
      WL_JMP(FID_wire_get_nat);
    } else {
      Term _o_50[1];
      if (spin_51(e, _o_50, term_ctr(CID_SCon, STAT_OFF + 1174)) == 0) {
        return 0;
      }
      r0 = _o_50[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1050)
    WL_POPN(1);
    Term _h_158 = STK(0);
    u32 _h_155 = r0;
    Term _h_156 = r1;
    Term _h_157 = r2;
    WL_OPEN
    if (_h_155 == 0) {
      if (seq) {
        WL_ROOM(3, 0);
        STK(0) = _h_158;
        STK(1) = _h_156;
        STK(2) = FID_ffi_go_k1051;
        WL_PUSHN(3);
      } else {
        u64 _t_58 = task_node(e, FID_ffi_go_k1051, WL_CONT, WL_IDX, 1);
        e.mem[_t_58 + 0] = _h_158;
        e.mem[_t_58 + 1] = _h_156;
        WL_CONT = term_tsk(FID_ffi_go_k1051, _t_58);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_progress_get_prior)) {
        u64 _t_59 = task_node(e, FID_ffi_progress_get_prior, WL_CONT, WL_IDX, 0);
        e.mem[_t_59 + 0] = _h_157;
        return term_tsk(FID_ffi_progress_get_prior, _t_59);
      }
      r0 = _h_157;
      WL_JMP(FID_ffi_progress_get_prior);
    } else {
      Term _o_49[1];
      if (spin_51(e, _o_49, term_ctr(CID_SCon, STAT_OFF + 826)) == 0) {
        return 0;
      }
      r0 = _o_49[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1051)
    WL_POPN(2);
    Term _h_164 = STK(0);
    Term _h_165 = STK(1);
    u32 _h_159 = r0;
    u32 _h_160 = r1;
    Term _h_161 = r2;
    Term _h_162 = r3;
    Term _h_163 = r4;
    WL_OPEN
    if (_h_159 == 0) {
      if (seq) {
        WL_ROOM(6, 0);
        STK(0) = _h_164;
        STK(1) = _h_165;
        STK(2) = _h_160;
        STK(3) = _h_161;
        STK(4) = _h_162;
        STK(5) = FID_ffi_go_k1052;
        WL_PUSHN(6);
      } else {
        u64 _t_60 = task_node(e, FID_ffi_go_k1052, WL_CONT, WL_IDX, 1);
        e.mem[_t_60 + 0] = _h_164;
        e.mem[_t_60 + 1] = _h_165;
        e.mem[_t_60 + 2] = _h_160;
        e.mem[_t_60 + 3] = _h_161;
        e.mem[_t_60 + 4] = _h_162;
        WL_CONT = term_tsk(FID_ffi_go_k1052, _t_60);
        WL_IDX = 5;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_nat)) {
        u64 _t_61 = task_node(e, FID_wire_get_nat, WL_CONT, WL_IDX, 0);
        e.mem[_t_61 + 0] = _h_163;
        return term_tsk(FID_wire_get_nat, _t_61);
      }
      r0 = _h_163;
      WL_JMP(FID_wire_get_nat);
    } else {
      Term _o_48[1];
      if (spin_51(e, _o_48, term_ctr(CID_SCon, STAT_OFF + 470)) == 0) {
        return 0;
      }
      r0 = _o_48[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1052)
    WL_POPN(5);
    Term _h_169 = STK(0);
    Term _h_170 = STK(1);
    u32 _h_171 = STK(2);
    Term _h_172 = STK(3);
    Term _h_173 = STK(4);
    u32 _h_166 = r0;
    Term _h_167 = r1;
    Term _h_168 = r2;
    WL_OPEN
    Term _o_47[1];
    if (spin_212(e, _o_47, _h_169, _h_170, _h_171, _h_172, _h_173, _h_166, _h_167, _h_168) == 0) {
      return 0;
    }
    r0 = _o_47[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1053)
    u32 _h_174 = r0;
    u32 _h_175 = r1;
    Term _h_176 = r2;
    u32 _h_177 = r3;
    u32 _h_178 = r4;
    u32 _h_179 = r5;
    u32 _h_180 = r6;
    Term _h_181 = r7;
    Term _h_182 = r8;
    WL_OPEN
    Term _o_52[1];
    if (spin_229(e, _o_52, _h_174, _h_175, _h_176, _h_177, _h_178, _h_179, _h_180, _h_181, _h_182) == 0) {
      return 0;
    }
    r0 = _o_52[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1054)
    u32 _h_183 = r0;
    u32 _h_184 = r1;
    Term _h_185 = r2;
    Term _h_186 = r3;
    Term _h_187 = r4;
    Term _h_188 = r5;
    Term _h_189 = r6;
    u32 _h_190 = r7;
    Term _h_191 = r8;
    Term _h_192 = r9;
    Term _h_193 = r10;
    WL_OPEN
    if (_h_183 == 0) {
      u32 _v_25 = 0;
      Term _o_54[1];
      if (spin_77(e, _o_54, _h_193) == 0) {
        return 0;
      }
      _v_25 = (u32)_o_54[0];
      if (_v_25 == 1) {
        if (_h_184 == 0) {
          u32 _v_26 = 0;
          Term _v_27 = 0;
          Term _v_28 = 0;
          Term _v_29 = 0;
          Term _v_30 = 0;
          Term _o_55[5];
          if (spin_205(e, _o_55, _h_185, _h_186, _h_187, _h_188) == 0) {
            return 0;
          }
          _v_26 = (u32)_o_55[0];
          _v_27 = _o_55[1];
          _v_28 = _o_55[2];
          _v_29 = _o_55[3];
          _v_30 = _o_55[4];
          Term _o_56[1];
          if (spin_206(e, _o_56, _v_26, _v_27, _v_28, _v_29, _v_30, term_pak(CID_SNil, 0)) == 0) {
            return 0;
          }
          r0 = _o_56[0];
          WL_RETN(1);
        } else if (_h_184 == 1) {
          u32 _v_31 = 0;
          Term _v_32 = 0;
          Term _v_33 = 0;
          Term _v_34 = 0;
          Term _o_57[4];
          if (spin_207(e, _o_57, _h_185, _h_186, _h_187, _h_188, _h_189, _h_190, _h_191, _h_192) == 0) {
            return 0;
          }
          _v_31 = (u32)_o_57[0];
          _v_32 = _o_57[1];
          _v_33 = _o_57[2];
          _v_34 = _o_57[3];
          Term _o_58[1];
          if (spin_180(e, _o_58, _v_31, _v_32, _v_33, _v_34, term_pak(CID_SNil, 0)) == 0) {
            return 0;
          }
          r0 = _o_58[0];
          WL_RETN(1);
        } else {
          if (seq) {
            WL_ROOM(6, 0);
            STK(0) = _h_185;
            STK(1) = _h_186;
            STK(2) = _h_187;
            STK(3) = _h_188;
            STK(4) = _h_189;
            STK(5) = FID_ffi_go_k1055;
            WL_PUSHN(6);
          } else {
            u64 _t_66 = task_node(e, FID_ffi_go_k1055, WL_CONT, WL_IDX, 1);
            e.mem[_t_66 + 0] = _h_185;
            e.mem[_t_66 + 1] = _h_186;
            e.mem[_t_66 + 2] = _h_187;
            e.mem[_t_66 + 3] = _h_188;
            e.mem[_t_66 + 4] = _h_189;
            WL_CONT = term_tsk(FID_ffi_go_k1055, _t_66);
            WL_IDX = 5;
          }
          if (!DEVICE && !seq && fid_nofk(FID_aux_fallback_put)) {
            u64 _t_67 = task_node(e, FID_aux_fallback_put, WL_CONT, WL_IDX, 0);
            e.mem[_t_67 + 0] = _h_185;
            e.mem[_t_67 + 1] = _h_186;
            e.mem[_t_67 + 2] = _h_187;
            e.mem[_t_67 + 3] = _h_188;
            e.mem[_t_67 + 4] = _h_189;
            e.mem[_t_67 + 5] = term_pak(CID_Nil, 0);
            return term_tsk(FID_aux_fallback_put, _t_67);
          }
          r0 = _h_185;
          r1 = _h_186;
          r2 = _h_187;
          r3 = _h_188;
          r4 = _h_189;
          r5 = term_pak(CID_Nil, 0);
          WL_JMP(FID_aux_fallback_put);
        }
      } else {
        term_sink(e, _h_189);
        Term _o_60[1];
        if (spin_51(e, _o_60, term_ctr(CID_SCon, STAT_OFF + 766)) == 0) {
          return 0;
        }
        r0 = _o_60[0];
        WL_RETN(1);
      }
    } else {
      Term _o_61[1];
      if (spin_51(e, _o_61, term_ctr(CID_SCon, STAT_OFF + 1112)) == 0) {
        return 0;
      }
      r0 = _o_61[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1055)
    WL_POPN(5);
    u32 _h_195 = STK(0);
    Term _h_196 = STK(1);
    Term _h_197 = STK(2);
    Term _h_198 = STK(3);
    Term _h_199 = STK(4);
    Term _h_194 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_194;
      STK(1) = FID_ffi_go_k1056;
      WL_PUSHN(2);
    } else {
      u64 _t_68 = task_node(e, FID_ffi_go_k1056, WL_CONT, WL_IDX, 1);
      e.mem[_t_68 + 0] = _h_194;
      WL_CONT = term_tsk(FID_ffi_go_k1056, _t_68);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_aux_fallback_after)) {
      u64 _t_69 = task_node(e, FID_aux_fallback_after, WL_CONT, WL_IDX, 0);
      e.mem[_t_69 + 0] = _h_195;
      e.mem[_t_69 + 1] = _h_196;
      e.mem[_t_69 + 2] = _h_197;
      e.mem[_t_69 + 3] = _h_198;
      e.mem[_t_69 + 4] = _h_199;
      return term_tsk(FID_aux_fallback_after, _t_69);
    }
    r0 = _h_195;
    r1 = _h_196;
    r2 = _h_197;
    r3 = _h_198;
    r4 = _h_199;
    WL_JMP(FID_aux_fallback_after);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1056)
    WL_POPN(1);
    Term _h_201 = STK(0);
    Term _h_200 = r0;
    WL_OPEN
    Term _rest_1 = term_pak(CID_SNil, 0);
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_201;
      STK(1) = FID_ffi_go_k1057;
      WL_PUSHN(2);
    } else {
      u64 _t_70 = task_node(e, FID_ffi_go_k1057, WL_CONT, WL_IDX, 1);
      e.mem[_t_70 + 0] = _h_201;
      WL_CONT = term_tsk(FID_ffi_go_k1057, _t_70);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_1)) {
      u64 _t_71 = task_node(e, FID_wire_put_list_1, WL_CONT, WL_IDX, 0);
      e.mem[_t_71 + 0] = _h_200;
      e.mem[_t_71 + 1] = _rest_1;
      return term_tsk(FID_wire_put_list_1, _t_71);
    }
    r0 = _h_200;
    r1 = _rest_1;
    WL_JMP(FID_wire_put_list_1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1057)
    WL_POPN(1);
    Term _h_203 = STK(0);
    Term _h_202 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_ffi_go_k1058;
      WL_PUSHN(1);
    } else {
      u64 _t_72 = task_node(e, FID_ffi_go_k1058, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_go_k1058, _t_72);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_go_2)) {
      u64 _t_73 = task_node(e, FID_wire_put_list_go_2, WL_CONT, WL_IDX, 0);
      e.mem[_t_73 + 0] = _h_203;
      e.mem[_t_73 + 1] = _h_202;
      return term_tsk(FID_wire_put_list_go_2, _t_73);
    }
    r0 = _h_203;
    r1 = _h_202;
    WL_JMP(FID_wire_put_list_go_2);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1058)
    Term _h_204 = r0;
    Term _h_205 = r1;
    WL_OPEN
    Term _o_59[1];
    if (spin_82(e, _o_59, _h_204, _h_205) == 0) {
      return 0;
    }
    r0 = _o_59[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1059)
    u32 _h_206 = r0;
    u32 _h_207 = r1;
    Term _h_208 = r2;
    Term _h_209 = r3;
    Term _h_210 = r4;
    Term _h_211 = r5;
    Term _h_212 = r6;
    Term _h_213 = r7;
    Term _h_214 = r8;
    WL_OPEN
    if (_h_206 == 0) {
      u32 _v_35 = 0;
      Term _o_63[1];
      if (spin_77(e, _o_63, _h_214) == 0) {
        return 0;
      }
      _v_35 = (u32)_o_63[0];
      if (_v_35 == 1) {
        if (_h_207 == 0) {
          if (seq) {
            WL_ROOM(1, 0);
            STK(0) = FID_ffi_go_k1060;
            WL_PUSHN(1);
          } else {
            u64 _t_76 = task_node(e, FID_ffi_go_k1060, WL_CONT, WL_IDX, 1);
            WL_CONT = term_tsk(FID_ffi_go_k1060, _t_76);
            WL_IDX = 0;
          }
          if (!DEVICE && !seq && fid_nofk(FID_workflow_admit)) {
            u64 _t_77 = task_node(e, FID_workflow_admit, WL_CONT, WL_IDX, 0);
            e.mem[_t_77 + 0] = _h_208;
            e.mem[_t_77 + 1] = _h_209;
            e.mem[_t_77 + 2] = _h_210;
            e.mem[_t_77 + 3] = _h_211;
            e.mem[_t_77 + 4] = _h_212;
            e.mem[_t_77 + 5] = _h_213;
            return term_tsk(FID_workflow_admit, _t_77);
          }
          r0 = _h_208;
          r1 = _h_209;
          r2 = _h_210;
          r3 = _h_211;
          r4 = _h_212;
          r5 = _h_213;
          WL_JMP(FID_workflow_admit);
        } else {
          Term _v_36 = 0;
          Term _v_37 = 0;
          Term _o_65[2];
          if (spin_203(e, _o_65, _h_208, _h_209, _h_210) == 0) {
            return 0;
          }
          _v_36 = _o_65[0];
          _v_37 = _o_65[1];
          Term _o_66[1];
          if (spin_204(e, _o_66, _v_36, _v_37, term_pak(CID_SNil, 0)) == 0) {
            return 0;
          }
          r0 = _o_66[0];
          WL_RETN(1);
        }
      } else {
        term_sink(e, _h_211);
        Term _o_67[1];
        if (spin_51(e, _o_67, term_ctr(CID_SCon, STAT_OFF + 742)) == 0) {
          return 0;
        }
        r0 = _o_67[0];
        WL_RETN(1);
      }
    } else {
      Term _o_68[1];
      if (spin_51(e, _o_68, term_ctr(CID_SCon, STAT_OFF + 1088)) == 0) {
        return 0;
      }
      r0 = _o_68[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1060)
    u32 _h_215 = r0;
    Term _h_216 = r1;
    Term _h_217 = r2;
    Term _h_218 = r3;
    WL_OPEN
    Term _o_64[1];
    if (spin_202(e, _o_64, _h_215, _h_216, _h_217, _h_218, term_pak(CID_SNil, 0)) == 0) {
      return 0;
    }
    r0 = _o_64[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1061)
    u32 _h_219 = r0;
    Term _h_220 = r1;
    Term _h_221 = r2;
    WL_OPEN
    if (_h_219 == 0) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _h_220;
        STK(1) = FID_ffi_go_k1062;
        WL_PUSHN(2);
      } else {
        u64 _t_80 = task_node(e, FID_ffi_go_k1062, WL_CONT, WL_IDX, 1);
        e.mem[_t_80 + 0] = _h_220;
        WL_CONT = term_tsk(FID_ffi_go_k1062, _t_80);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_wire_get_list_4)) {
        u64 _t_81 = task_node(e, FID_wire_get_list_4, WL_CONT, WL_IDX, 0);
        e.mem[_t_81 + 0] = _h_221;
        return term_tsk(FID_wire_get_list_4, _t_81);
      }
      r0 = _h_221;
      WL_JMP(FID_wire_get_list_4);
    } else {
      Term _o_74[1];
      if (spin_51(e, _o_74, term_ctr(CID_SCon, STAT_OFF + 1050)) == 0) {
        return 0;
      }
      r0 = _o_74[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1062)
    WL_POPN(1);
    Term _h_225 = STK(0);
    u32 _h_222 = r0;
    Term _h_223 = r1;
    Term _h_224 = r2;
    WL_OPEN
    if (_h_222 == 0) {
      u32 _v_38 = 0;
      Term _o_70[1];
      if (spin_77(e, _o_70, _h_224) == 0) {
        return 0;
      }
      _v_38 = (u32)_o_70[0];
      if (_v_38 == 1) {
        if (seq) {
          WL_ROOM(1, 0);
          STK(0) = FID_ffi_go_k1063;
          WL_PUSHN(1);
        } else {
          u64 _t_82 = task_node(e, FID_ffi_go_k1063, WL_CONT, WL_IDX, 1);
          WL_CONT = term_tsk(FID_ffi_go_k1063, _t_82);
          WL_IDX = 0;
        }
        if (!DEVICE && !seq && fid_nofk(FID_doc_seen_check)) {
          u64 _t_83 = task_node(e, FID_doc_seen_check, WL_CONT, WL_IDX, 0);
          e.mem[_t_83 + 0] = _h_225;
          e.mem[_t_83 + 1] = _h_223;
          return term_tsk(FID_doc_seen_check, _t_83);
        }
        r0 = _h_225;
        r1 = _h_223;
        WL_JMP(FID_doc_seen_check);
      } else {
        term_sink(e, _h_225);
        term_sink(e, _h_223);
        Term _o_72[1];
        if (spin_51(e, _o_72, term_ctr(CID_SCon, STAT_OFF + 424)) == 0) {
          return 0;
        }
        r0 = _o_72[0];
        WL_RETN(1);
      }
    } else {
      term_sink(e, _h_225);
      Term _o_73[1];
      if (spin_51(e, _o_73, term_ctr(CID_SCon, STAT_OFF + 726)) == 0) {
        return 0;
      }
      r0 = _o_73[0];
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1063)
    Term _h_226 = r0;
    Term _h_227 = r1;
    u32 _h_228 = r2;
    WL_OPEN
    Term _rest_2 = term_pak(CID_SNil, 0);
    Term _v_39 = 0;
    Term _o_71[1];
    if (spin_147(e, _o_71, _h_228, _rest_2) == 0) {
      return 0;
    }
    _v_39 = _o_71[0];
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _h_226;
      STK(1) = FID_ffi_go_k1064;
      WL_PUSHN(2);
    } else {
      u64 _t_84 = task_node(e, FID_ffi_go_k1064, WL_CONT, WL_IDX, 1);
      e.mem[_t_84 + 0] = _h_226;
      WL_CONT = term_tsk(FID_ffi_go_k1064, _t_84);
      WL_IDX = 1;
    }
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_6)) {
      u64 _t_85 = task_node(e, FID_wire_put_list_6, WL_CONT, WL_IDX, 0);
      e.mem[_t_85 + 0] = _h_227;
      e.mem[_t_85 + 1] = _v_39;
      return term_tsk(FID_wire_put_list_6, _t_85);
    }
    r0 = _h_227;
    r1 = _v_39;
    WL_JMP(FID_wire_put_list_6);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_ffi_go_k1064)
    WL_POPN(1);
    Term _h_230 = STK(0);
    Term _h_229 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_wire_put_list_5)) {
      u64 _t_86 = task_node(e, FID_wire_put_list_5, WL_CONT, WL_IDX, 0);
      e.mem[_t_86 + 0] = _h_230;
      e.mem[_t_86 + 1] = _h_229;
      return term_tsk(FID_wire_put_list_5, _t_86);
    }
    r0 = _h_230;
    r1 = _h_229;
    WL_JMP(FID_wire_put_list_5);
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
        STK(0) = FID_open_go_k1068;
        WL_PUSHN(1);
      } else {
        u64 _t_0 = task_node(e, FID_open_go_k1068, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_open_go_k1068, _t_0);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_echo_open)) {
        u64 _t_1 = task_node(e, FID_ffi_echo_open, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _input_0;
        return term_tsk(FID_ffi_echo_open, _t_1);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_echo_open);
    } else if (_entry_0 == 2) {
      if (seq) {
        WL_ROOM(1, 0);
        STK(0) = FID_open_go_k1069;
        WL_PUSHN(1);
      } else {
        u64 _t_2 = task_node(e, FID_open_go_k1069, WL_CONT, WL_IDX, 1);
        WL_CONT = term_tsk(FID_open_go_k1069, _t_2);
        WL_IDX = 0;
      }
      if (!DEVICE && !seq && fid_nofk(FID_ffi_admission_open)) {
        u64 _t_3 = task_node(e, FID_ffi_admission_open, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _input_0;
        return term_tsk(FID_ffi_admission_open, _t_3);
      }
      r0 = _input_0;
      WL_JMP(FID_ffi_admission_open);
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
      r0 = 2;
      r1 = 0;
      r2 = 0;
      r3 = 0;
      r4 = 0;
      r5 = 0;
      r6 = 0;
      r7 = term_ctr(CID_SCon, STAT_OFF + 1498);
      WL_RETN(8);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_go_k1068)
    u32 _h_0 = r0;
    Term _h_1 = r1;
    Term _h_2 = r2;
    Term _h_3 = r3;
    WL_OPEN
    Term _o_0[8];
    if (spin_233(e, _o_0, _h_0, _h_1, _h_2, _h_3) == 0) {
      return 0;
    }
    r0 = (u32)_o_0[0];
    r1 = (u32)_o_0[1];
    r2 = _o_0[2];
    r3 = _o_0[3];
    r4 = _o_0[4];
    r5 = _o_0[5];
    r6 = _o_0[6];
    r7 = _o_0[7];
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_open_go_k1069)
    u32 _h_4 = r0;
    u32 _h_5 = r1;
    Term _h_6 = r2;
    Term _h_7 = r3;
    Term _h_8 = r4;
    Term _h_9 = r5;
    Term _h_10 = r6;
    WL_OPEN
    Term _o_1[8];
    if (spin_234(e, _o_1, _h_4, _h_5, _h_6, _h_7, _h_8, _h_9, _h_10) == 0) {
      return 0;
    }
    r0 = (u32)_o_1[0];
    r1 = (u32)_o_1[1];
    r2 = _o_1[2];
    r3 = _o_1[3];
    r4 = _o_1[4];
    r5 = _o_1[5];
    r6 = _o_1[6];
    r7 = _o_1[7];
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step)
    u32 _state_0 = r0;
    u32 _state_1 = r1;
    Term _state_2 = r2;
    Term _state_3 = r3;
    Term _state_4 = r4;
    Term _state_5 = r5;
    Term _state_6 = r6;
    Term _input_0 = r7;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_step_k1071;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_step_k1071, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_step_k1071, _t_0);
      WL_IDX = 0;
    }
    if (!DEVICE && !seq && fid_nofk(FID_step_go)) {
      u64 _t_1 = task_node(e, FID_step_go, WL_CONT, WL_IDX, 0);
      e.mem[_t_1 + 0] = _state_0;
      e.mem[_t_1 + 1] = _state_1;
      e.mem[_t_1 + 2] = _state_2;
      e.mem[_t_1 + 3] = _state_3;
      e.mem[_t_1 + 4] = _state_4;
      e.mem[_t_1 + 5] = _state_5;
      e.mem[_t_1 + 6] = _state_6;
      e.mem[_t_1 + 7] = _input_0;
      return term_tsk(FID_step_go, _t_1);
    }
    r0 = _state_0;
    r1 = _state_1;
    r2 = _state_2;
    r3 = _state_3;
    r4 = _state_4;
    r5 = _state_5;
    r6 = _state_6;
    r7 = _input_0;
    WL_JMP(FID_step_go);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_step_k1071)
    u32 _r_0 = r0;
    u32 _r_1 = r1;
    Term _r_2 = r2;
    Term _r_3 = r3;
    Term _r_4 = r4;
    Term _r_5 = r5;
    Term _r_6 = r6;
    Term _r_7 = r7;
    WL_OPEN
    r0 = _r_0;
    r1 = _r_1;
    r2 = _r_2;
    r3 = _r_3;
    r4 = _r_4;
    r5 = _r_5;
    r6 = _r_6;
    r7 = _r_7;
    WL_RETN(8);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_close)
    u32 _state_0 = r0;
    u32 _state_1 = r1;
    Term _state_2 = r2;
    Term _state_3 = r3;
    Term _state_4 = r4;
    Term _state_5 = r5;
    Term _state_6 = r6;
    WL_OPEN
    Term _v_0 = 0;
    Term _o_0[1];
    if (spin_235(e, _o_0, _state_0, _state_1, _state_2, _state_3, _state_4, _state_5, _state_6) == 0) {
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
      STK(0) = FID_ffi_k1075;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_ffi_k1075, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_ffi_k1075, _t_0);
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
  WL_CASE(FID_ffi_k1075)
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
      STK(0) = FID_open_k1080;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_open_k1080, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_open_k1080, _t_0);
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
  WL_CASE(FID_open_k1080)
    u32 _r_0 = r0;
    u32 _r_1 = r1;
    Term _r_2 = r2;
    Term _r_3 = r3;
    Term _r_4 = r4;
    Term _r_5 = r5;
    Term _r_6 = r6;
    Term _r_7 = r7;
    WL_OPEN
    r0 = _r_0;
    r1 = _r_1;
    r2 = _r_2;
    r3 = _r_3;
    r4 = _r_4;
    r5 = _r_5;
    r6 = _r_6;
    r7 = _r_7;
    WL_RETN(8);
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
    Term _r_5 = r6;
    Term _r_6 = r7;
    Term _r_7 = r8;
    WL_OPEN
    if (term_aux(_events_0) == CID_Nil) {
      if (seq) {
        WL_ROOM(2, 0);
        STK(0) = _r_7;
        STK(1) = FID_cli_steps_k1082;
        WL_PUSHN(2);
      } else {
        u64 _t_0 = task_node(e, FID_cli_steps_k1082, WL_CONT, WL_IDX, 1);
        e.mem[_t_0 + 0] = _r_7;
        WL_CONT = term_tsk(FID_cli_steps_k1082, _t_0);
        WL_IDX = 1;
      }
      if (!DEVICE && !seq && fid_nofk(FID_close)) {
        u64 _t_1 = task_node(e, FID_close, WL_CONT, WL_IDX, 0);
        e.mem[_t_1 + 0] = _r_0;
        e.mem[_t_1 + 1] = _r_1;
        e.mem[_t_1 + 2] = _r_2;
        e.mem[_t_1 + 3] = _r_3;
        e.mem[_t_1 + 4] = _r_4;
        e.mem[_t_1 + 5] = _r_5;
        e.mem[_t_1 + 6] = _r_6;
        return term_tsk(FID_close, _t_1);
      }
      r0 = _r_0;
      r1 = _r_1;
      r2 = _r_2;
      r3 = _r_3;
      r4 = _r_4;
      r5 = _r_5;
      r6 = _r_6;
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
        STK(1) = _r_7;
        STK(2) = FID_cli_steps_k1083;
        WL_PUSHN(3);
      } else {
        u64 _t_2 = task_node(e, FID_cli_steps_k1083, WL_CONT, WL_IDX, 1);
        e.mem[_t_2 + 0] = _f_1;
        e.mem[_t_2 + 1] = _r_7;
        WL_CONT = term_tsk(FID_cli_steps_k1083, _t_2);
        WL_IDX = 2;
      }
      if (!DEVICE && !seq && fid_nofk(FID_step)) {
        u64 _t_3 = task_node(e, FID_step, WL_CONT, WL_IDX, 0);
        e.mem[_t_3 + 0] = _r_0;
        e.mem[_t_3 + 1] = _r_1;
        e.mem[_t_3 + 2] = _r_2;
        e.mem[_t_3 + 3] = _r_3;
        e.mem[_t_3 + 4] = _r_4;
        e.mem[_t_3 + 5] = _r_5;
        e.mem[_t_3 + 6] = _r_6;
        e.mem[_t_3 + 7] = _f_0;
        return term_tsk(FID_step, _t_3);
      }
      r0 = _r_0;
      r1 = _r_1;
      r2 = _r_2;
      r3 = _r_3;
      r4 = _r_4;
      r5 = _r_5;
      r6 = _r_6;
      r7 = _f_0;
      WL_JMP(FID_step);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k1082)
    WL_POPN(1);
    Term _r_8 = STK(0);
    Term _h_0 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_237(e, _o_0, _r_8) == 0) {
      return 0;
    }
    r0 = _o_0[0];
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k1083)
    WL_POPN(2);
    Term _f_2 = STK(0);
    Term _r_9 = STK(1);
    u32 _h_1 = r0;
    u32 _h_2 = r1;
    Term _h_3 = r2;
    Term _h_4 = r3;
    Term _h_5 = r4;
    Term _h_6 = r5;
    Term _h_7 = r6;
    Term _h_8 = r7;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _r_9;
      STK(1) = FID_cli_steps_k1084;
      WL_PUSHN(2);
    } else {
      u64 _t_4 = task_node(e, FID_cli_steps_k1084, WL_CONT, WL_IDX, 1);
      e.mem[_t_4 + 0] = _r_9;
      WL_CONT = term_tsk(FID_cli_steps_k1084, _t_4);
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
      e.mem[_t_5 + 6] = _h_6;
      e.mem[_t_5 + 7] = _h_7;
      e.mem[_t_5 + 8] = _h_8;
      return term_tsk(FID_cli_steps, _t_5);
    }
    r0 = _f_2;
    r1 = _h_1;
    r2 = _h_2;
    r3 = _h_3;
    r4 = _h_4;
    r5 = _h_5;
    r6 = _h_6;
    r7 = _h_7;
    r8 = _h_8;
    WL_JMP(FID_cli_steps);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_steps_k1084)
    WL_POPN(1);
    Term _r_10 = STK(0);
    Term _h_9 = r0;
    WL_OPEN
    u64 _nd_1 = heap_alloc(e, cls_fit(2));
    e.mem[_nd_1 + 0] = rfc_seal(e, _r_10);
    e.mem[_nd_1 + 1] = rfc_seal(e, _h_9);
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
      r0 = term_clo(FID_cli_print_c1096, 0);
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
      r0 = term_clo(FID_cli_print_c1097, _nd_0);
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c1096)
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
  WL_CASE(FID_cli_print_c1097)
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
      e.mem[_t_2 + 1] = term_clo(FID_cli_print_c1098, _nd_2);
      e.mem[_t_2 + 2] = _x_2;
      return term_tsk(FID_IO_bind, _t_2);
    }
    r0 = term_clo(FID_IO_print, _nd_1);
    r1 = term_clo(FID_cli_print_c1098, _nd_2);
    r2 = _x_2;
    WL_JMP(FID_IO_bind);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_print_c1098)
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
              STK(3) = FID_cli_args_k1100;
              WL_PUSHN(4);
            } else {
              u64 _t_0 = task_node(e, FID_cli_args_k1100, WL_CONT, WL_IDX, 1);
              e.mem[_t_0 + 0] = _f_2;
              e.mem[_t_0 + 1] = _f_6;
              e.mem[_t_0 + 2] = _f_7;
              WL_CONT = term_tsk(FID_cli_args_k1100, _t_0);
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
  WL_CASE(FID_cli_args_k1100)
    WL_POPN(3);
    Term _f_8 = STK(0);
    Term _f_9 = STK(1);
    Term _f_10 = STK(2);
    u32 _h_0 = r0;
    u32 _h_1 = r1;
    WL_OPEN
    u32 _v_0 = 0;
    Term _o_2[1];
    if (spin_239(e, _o_2, _f_8, term_ctr(CID_SCon, STAT_OFF + 1502)) == 0) {
      return 0;
    }
    _v_0 = (u32)_o_2[0];
    u32 _v_2 = 0;
    Term _o_3[1];
    if (spin_239(e, _o_3, _f_8, term_ctr(CID_SCon, STAT_OFF + 1284)) == 0) {
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
              STK(0) = FID_cli_args_k1101;
              WL_PUSHN(1);
            } else {
              u64 _t_2 = task_node(e, FID_cli_args_k1101, WL_CONT, WL_IDX, 1);
              WL_CONT = term_tsk(FID_cli_args_k1101, _t_2);
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
            STK(1) = FID_cli_args_k1102;
            WL_PUSHN(2);
          } else {
            u64 _t_4 = task_node(e, FID_cli_args_k1102, WL_CONT, WL_IDX, 1);
            e.mem[_t_4 + 0] = _f_10;
            WL_CONT = term_tsk(FID_cli_args_k1102, _t_4);
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
  WL_CASE(FID_cli_args_k1101)
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
  WL_CASE(FID_cli_args_k1102)
    WL_POPN(1);
    Term _f_13 = STK(0);
    u32 _h_3 = r0;
    u32 _h_4 = r1;
    Term _h_5 = r2;
    Term _h_6 = r3;
    Term _h_7 = r4;
    Term _h_8 = r5;
    Term _h_9 = r6;
    Term _h_10 = r7;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_cli_args_k1103;
      WL_PUSHN(1);
    } else {
      u64 _t_6 = task_node(e, FID_cli_args_k1103, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_cli_args_k1103, _t_6);
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
      e.mem[_t_7 + 6] = _h_8;
      e.mem[_t_7 + 7] = _h_9;
      e.mem[_t_7 + 8] = _h_10;
      return term_tsk(FID_cli_steps, _t_7);
    }
    r0 = _f_13;
    r1 = _h_3;
    r2 = _h_4;
    r3 = _h_5;
    r4 = _h_6;
    r5 = _h_7;
    r6 = _h_8;
    r7 = _h_9;
    r8 = _h_10;
    WL_JMP(FID_cli_steps);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_cli_args_k1103)
    Term _h_11 = r0;
    WL_OPEN
    r0 = 1;
    r1 = _h_11;
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
      e.mem[_t_3 + 1] = term_clo(FID_IO_bind_c1107, _nd_0);
      return term_tsk(FID_Clo_apply, _t_3);
    }
    r0 = _m_0;
    r1 = term_clo(FID_IO_bind_c1107, _nd_0);
    WL_JMP(FID_Clo_apply);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_IO_bind_c1107)
    Term _f_1 = r0;
    Term _k_1 = r1;
    Term _x_0 = r2;
    WL_OPEN
    if (seq) {
      WL_ROOM(2, 0);
      STK(0) = _k_1;
      STK(1) = FID_IO_bind_k1108;
      WL_PUSHN(2);
    } else {
      u64 _t_0 = task_node(e, FID_IO_bind_k1108, WL_CONT, WL_IDX, 1);
      e.mem[_t_0 + 0] = _k_1;
      WL_CONT = term_tsk(FID_IO_bind_k1108, _t_0);
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
  WL_CASE(FID_IO_bind_k1108)
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
    r0 = term_clo(FID_main_c1110, 0);
    WL_RETN(1);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c1110)
    Term _x_0 = r0;
    WL_OPEN
    if (!DEVICE && !seq && fid_nofk(FID_IO_bind)) {
      u64 _t_3 = task_node(e, FID_IO_bind, WL_CONT, WL_IDX, 0);
      e.mem[_t_3 + 0] = term_clo(FID_IO_args, 0);
      e.mem[_t_3 + 1] = term_clo(FID_main_c1111, 0);
      e.mem[_t_3 + 2] = _x_0;
      return term_tsk(FID_IO_bind, _t_3);
    }
    r0 = term_clo(FID_IO_args, 0);
    r1 = term_clo(FID_main_c1111, 0);
    r2 = _x_0;
    WL_JMP(FID_IO_bind);
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c1111)
    Term _x_1 = r0;
    WL_OPEN
    if (seq) {
      WL_ROOM(1, 0);
      STK(0) = FID_main_k1112;
      WL_PUSHN(1);
    } else {
      u64 _t_0 = task_node(e, FID_main_k1112, WL_CONT, WL_IDX, 1);
      WL_CONT = term_tsk(FID_main_k1112, _t_0);
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
  WL_CASE(FID_main_k1112)
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
      r0 = term_clo(FID_main_c1113, 0);
      WL_RETN(1);
    }
  }}
#endif

#if !DEVICE
  WL_CASE(FID_main_c1113)
    Term _x_2 = r0;
    WL_OPEN
    Term _o_0[1];
    if (spin_240(e, _o_0, 2ull, term_ctr(CID_SCon, STAT_OFF + 1648), _x_2) == 0) {
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
