// The C boundary of the compiled Bend core (crates/eukhe-bend).
//
// core.c is `bend bend/core.bend -o core.c` (scripts/bend_core.py, Bend
// 2.0.38): the Bend runtime plus every def bend/core.bend reaches. This file
// includes it in the same translation unit (its `main`, the debugging CLI, is
// renamed away) and drives it with the runtime's own functions, the ones its
// io_loop and its effects (`bend guide effects`) use. Bend makes no ABI
// promise: a Bend update regenerates core.c and re-checks this file.
//
// Init, once, on the first entry (under eb_lock):
//   eb_corpus_setup()          the heap: corpus_setup(false, 1, 0) of the
//                              runtime with a smaller first reservation,
//                              EB_HEAP_BYTES (512 MiB MAP_NORESERVE instead
//                              of 8 GiB), so a process under an address-space
//                              cap (ulimit -v, RLIMIT_AS) can still map it;
//                              the runtime doubles it in place on demand
//                              (corpus_grow, up to 8 TiB) as for its own
//                              heap; one lane, so pool_open never starts a
//                              pool thread;
//   eb_stack()                 the evaluation stack io_stk: pool_stack() of
//                              the runtime with EB_STACK_BYTES (256 MiB
//                              MAP_NORESERVE, then a guard page) for its
//                              2 GiB, and without its SIGSEGV/SIGBUS handler
//                              and alternate signal stack: the host (Rust)
//                              keeps its own. A run past the guard faults
//                              and ends the process, as in the runtime.
// An evaluation (under eb_lock):
//   io_str(e, bytes, n)         the input String on the heap (UTF-8 decoded
//                               as WHATWG does: an invalid sequence becomes
//                               U+FFFD; Rust passes a &str, always valid);
//   task_node + corpus_eval     run the entry's segment to its result;
//   io_cstr(e, reply, &n)       the reply String as a malloc'd UTF-8 buffer
//                               (NUL-terminated); it frees the String's cells.
// The buffer goes to the caller, who releases it with eukhe_bend_free.
//
// The entries are the segments of bend/core.bend's `ffi`, `open`, `step` and
// `close`. A def's arguments and results travel flattened, a word each: a
// record or a sum takes several words (a sum: its constructor index, then
// the fields), and `State & String` is the State's words, then the String's
// one. So a stepper's state is K words, K = the arity of `step` less its
// input; a slot keeps them between calls. eb_init checks every segment's
// shape against K once.
//
// The runtime's fail-stops (err_fail: a Nat past 2^48-1, a failed
// reservation, a lost delivery; err_trap: a fault) print `bend: ...` and
// _exit(1): they end the host process. Inputs must be bounded so that a pure
// evaluation cannot reach them.
//
// Fork: the state lives in this process (the heap, the stack and eb_lock). A
// child forked while another thread holds eb_lock inherits it locked; a child
// that execs at once (std::process::Command) never touches it.

// The emitted C passes its whole register bank on every jump, so most
// segments get registers they never read or set; the runtime keeps helpers a
// given program does not use, writes one-line `if (..) break; x = ..;`
// macros, and its thread loops never return. Those warnings of -Wall -Wextra
// are silenced for core.c alone; this file keeps them all.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-function"
#pragma GCC diagnostic ignored "-Wuninitialized"
#pragma GCC diagnostic ignored "-Wmisleading-indentation"
#pragma GCC diagnostic ignored "-Wreturn-type"
#ifdef __clang__
#pragma clang diagnostic ignored "-Wsometimes-uninitialized"
#else
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#pragma GCC diagnostic ignored "-Wunknown-pragmas"
#endif
#define main eukhe_bend_cli_main
#include "core.c"
#undef main
#pragma GCC diagnostic pop

#define EB_ABI    1  // the core's segments do not have the shapes this shim expects
#define EB_HANDLE 2  // no open state has this handle
#define EB_NOMEM  3  // the slot table could not grow

typedef struct {
  u32  gen;   // bumped by every close: a handle names one generation of a slot
  u32  next;  // while free: the next free slot + 1 (0: none)
  bool live;
} EbSlot;

static pthread_mutex_t eb_lock = PTHREAD_MUTEX_INITIALIZER;
static bool            eb_ready;  // eb_init ran
static u32             eb_fault;  // 0, or EB_ABI
static u64*            eb_heap;
static u32             eb_words;  // K: the words of a state
static EbSlot*         eb_slots;
static Term*           eb_state;  // K words per slot (one when K is 0)
static u32             eb_cap;
static u32             eb_free;   // the first free slot + 1 (0: none)

// The first reservation of the heap. The runtime's own corpus_setup maps
// 8 GiB; the rules of eukhe live in a few MiB, and the heap grows by
// doubling in place when an evaluation needs more.
#define EB_HEAP_BYTES (1ull << 29)

// corpus_setup(false, 1, 0) of core.c (Bend 2.0.38) with EB_HEAP_BYTES for
// its fixed 1 << 33: the same steps in the same order.
static u64* eb_corpus_setup(void) {
  io_gpu     = false;
  KEEP_WORDS = CAP_WORDS;
  u64 size   = EB_HEAP_BYTES & ~16383ull;
  CORPUS     = corpus_map(size);
  u64* H     = CORPUS;
  corpus_lay(H, size);
  memcpy(H + STAT_OFF, STAT_IMG, STAT_LEN * sizeof(u64));
  a32_store(a32_at(H, H_BUMP), 1);
  pool_size = 1;
  return H;
}

// The evaluation stack: frames of non-tail recursion (a decoder reading a
// String takes one per char). 256 MiB holds tens of millions of frames.
#define EB_STACK_BYTES (1ull << 28)

// pool_stack() of core.c (Bend 2.0.38) with EB_STACK_BYTES for its 1 << 31,
// the guard page kept, the signal setup left to the host.
static Term* eb_stack(void) {
  char* p = pool_mmap(EB_STACK_BYTES + 16384);
  if (mprotect(p + EB_STACK_BYTES, 16384, PROT_NONE)) {
    err_fail("stack guard failed");
  }
  return (Term*)p;
}

static u32 eb_init(void) {
  if (eb_ready) {
    return eb_fault;
  }
  eb_ready = true;
  // FID_T carries arities (not result widths, which are 0 on the CPU), so the
  // widths follow from the types: `State & String` is K + 1 words, and the
  // widest result (WL_RESW) holds it.
  u32 k = fid_arity(FID_step) == 0 ? 0 : fid_arity(FID_step) - 1;
  bool shaped = fid_arity(FID_step) == k + 1 && k + 1 <= WL_RESW
    && fid_arity(FID_open) == 2 && fid_arity(FID_close) == k
    && fid_arity(FID_ffi) == 2;
  if (!shaped) {
    eb_fault = EB_ABI;
    return eb_fault;
  }
  eb_words = k;
  eb_heap = eb_corpus_setup();
  io_stk  = eb_stack();
  return 0;
}

static Env eb_env(void) {
  return (Env){ eb_heap, ALC[0] };
}

// Runs segment fid on its fid_arity(fid) argument words; out receives its
// first `width` result words. corpus_eval answers the first; root_take left
// all of them at H_ROOT_WORD.
static void eb_eval(u32 fid, const Term* args, Term* out, u32 width) {
  Env e   = eb_env();
  u64 loc = task_node(e, fid, TERM_HOLE, 0, 0);
  for (u32 i = 0; i < fid_arity(fid); i += 1) {
    e.mem[loc + i] = args[i];
  }
  out[0] = corpus_eval(eb_heap, term_tsk(fid, loc));
  for (u32 j = 1; j < width; j += 1) {
    out[j] = eb_heap[H_ROOT_WORD + j];
  }
}

// The reply String as a malloc'd buffer. NULL when the word is no String (the
// result layout is not the one eb_init derived): *out_n holds EB_ABI, and
// every later entry answers EB_ABI.
static char* eb_reply(Term s, uint64_t* out_n) {
  bool str = (term_tag(s) == TAG_PAK && term_aux(s) == CID_SNil)
    || (term_tag(s) == TAG_CTR && term_aux(s) == CID_SCon);
  if (!str) {
    eb_fault = EB_ABI;
    *out_n   = EB_ABI;
    return NULL;
  }
  u64   n    = 0;
  char* text = io_cstr(eb_env(), s, &n);
  *out_n     = n;
  return text;
}

// Drops a state's K words (bend/core.bend's `close`).
static void eb_drop(const Term* st) {
  Term out[WL_RESW];
  eb_eval(FID_close, st, out, 1);
  term_sink(eb_env(), out[0]);
}

static Term* eb_words_of(u32 slot) {
  return eb_state + (u64)slot * (eb_words > 0 ? eb_words : 1);
}

// The slot of a live handle, or -1.
static int64_t eb_slot(uint64_t handle) {
  u32 idx = (u32)handle;
  u32 gen = (u32)(handle >> 32);
  if (!eb_ready || eb_fault != 0 || idx == 0 || idx > eb_cap) {
    return -1;
  }
  EbSlot* s = &eb_slots[idx - 1];
  return s->live && s->gen == gen ? (int64_t)(idx - 1) : -1;
}

// A free slot, made live; -1 when the table cannot grow.
static int64_t eb_take(void) {
  if (eb_free == 0) {
    if (eb_cap >= 1u << 30) {
      return -1;
    }
    u32     cap   = eb_cap == 0 ? 16 : eb_cap * 2;
    u64     per   = eb_words > 0 ? eb_words : 1;
    EbSlot* slots = realloc(eb_slots, cap * sizeof(EbSlot));
    if (slots == NULL) {
      return -1;
    }
    eb_slots    = slots;
    Term* state = realloc(eb_state, cap * per * sizeof(Term));
    if (state == NULL) {
      return -1;
    }
    eb_state = state;
    for (u32 i = cap; i > eb_cap; i -= 1) {
      eb_slots[i - 1] = (EbSlot){ .gen = 1, .next = eb_free, .live = false };
      eb_free         = i;
    }
    eb_cap = cap;
  }
  u32 idx            = eb_free - 1;
  eb_free            = eb_slots[idx].next;
  eb_slots[idx].live = true;
  return idx;
}

// call: the reply of entry's `ffi` to input (n bytes of UTF-8), a malloc'd
// UTF-8 buffer of *out_n bytes, NUL-terminated. NULL: *out_n holds EB_ABI.
char* eukhe_bend_call(uint32_t entry, const char* in, uint64_t n, uint64_t* out_n) {
  pthread_mutex_lock(&eb_lock);
  char* text  = NULL;
  u32   fault = eb_init();
  if (fault != 0) {
    *out_n = fault;
  } else {
    Term args[2] = { (Term)entry, io_str(eb_env(), in, n) };
    Term res[WL_RESW];
    eb_eval(FID_ffi, args, res, 1);
    text = eb_reply(res[0], out_n);
  }
  pthread_mutex_unlock(&eb_lock);
  return text;
}

// open: a new state of entry's stepper (an unknown entry's state answers the
// error form). Answers its handle, never 0, and the reply in *out (*out_n
// bytes, as eukhe_bend_call). 0: *out is NULL and *out_n holds EB_ABI or
// EB_NOMEM.
uint64_t eukhe_bend_open(uint32_t entry, const char* in, uint64_t n, char** out,
  uint64_t* out_n) {
  pthread_mutex_lock(&eb_lock);
  uint64_t handle = 0;
  u32      fault  = eb_init();
  *out            = NULL;
  if (fault != 0) {
    *out_n = fault;
  } else {
    Term args[2] = { (Term)entry, io_str(eb_env(), in, n) };
    Term res[WL_RESW];
    eb_eval(FID_open, args, res, eb_words + 1);
    // res: the state's K words, then the reply.
    *out = eb_reply(res[eb_words], out_n);
    int64_t slot = *out == NULL ? -1 : eb_take();
    if (*out != NULL && slot < 0) {
      eb_drop(res);
      free(*out);
      *out   = NULL;
      *out_n = EB_NOMEM;
    } else if (*out != NULL) {
      memcpy(eb_words_of((u32)slot), res, eb_words * sizeof(Term));
      handle = (uint64_t)eb_slots[slot].gen << 32 | (uint64_t)(slot + 1);
    }
  }
  pthread_mutex_unlock(&eb_lock);
  return handle;
}

// step: feeds input to the state of handle; the state step answers replaces
// it (the old one is consumed). 0 with the reply in *out (as eukhe_bend_open);
// EB_HANDLE when no open state has this handle, EB_ABI (*out NULL).
int eukhe_bend_step(uint64_t handle, const char* in, uint64_t n, char** out, uint64_t* out_n) {
  pthread_mutex_lock(&eb_lock);
  int     rc   = 0;
  int64_t slot = eb_slot(handle);
  *out         = NULL;
  if (eb_fault != 0) {
    rc = EB_ABI;
  } else if (slot < 0) {
    rc = EB_HANDLE;
  } else {
    Term* st = eb_words_of((u32)slot);
    Term  args[256];
    Term  res[WL_RESW];
    memcpy(args, st, eb_words * sizeof(Term));
    args[eb_words] = io_str(eb_env(), in, n);
    eb_eval(FID_step, args, res, eb_words + 1);
    memcpy(st, res, eb_words * sizeof(Term));
    *out = eb_reply(res[eb_words], out_n);
    rc   = *out == NULL ? EB_ABI : 0;
  }
  pthread_mutex_unlock(&eb_lock);
  return rc;
}

// close: drops the state of handle and frees its slot; a handle of no open
// state is left alone.
void eukhe_bend_close(uint64_t handle) {
  pthread_mutex_lock(&eb_lock);
  int64_t slot = eb_slot(handle);
  if (slot >= 0) {
    eb_drop(eb_words_of((u32)slot));
    EbSlot* s = &eb_slots[slot];
    s->live   = false;
    s->gen   += 1;
    s->next   = eb_free;
    eb_free   = (u32)slot + 1;
  }
  pthread_mutex_unlock(&eb_lock);
}

// Releases a reply buffer of eukhe_bend_call, eukhe_bend_open or
// eukhe_bend_step.
void eukhe_bend_free(char* text) {
  free(text);
}
