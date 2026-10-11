/* Host harness for emitted Ember code (plan M2.7).
 *
 *   harness [-p K] inputs.trace          one run, trace on stdout
 *   harness --batch LIST                 lines "K inputs.trace output.trace"
 *                                        (each run in a forked child, so
 *                                        every run starts from the initial
 *                                        globals)
 *
 * Reads the `rx`/`tick` lines of a §3.1 trace as the input oracle, calls
 * program K's entry while input remains (stopping after three calls in a
 * row that consume nothing, as `Ember.Lang.runMachine` does), and writes
 * the same trace the interpreter writes: every input line followed by
 * the events attributed to it.  A trap is reported as a final
 * `note trap ...` line and exit status 3.
 *
 * EMBER_TRACE=0 omits drop/note lines; 2 (default) keeps them. */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include <unistd.h>
#include <sys/wait.h>
#include "ember_rt.h"

#ifndef EMBER_TRACE
#define EMBER_TRACE 2
#endif

typedef struct {
  void (*entry)(void);
  const char *const *drops; const unsigned *ndrops;
  const char *const *notes; const unsigned *nnotes;
  const unsigned *framed;
} ember_prog;
extern const ember_prog ember_progs[];
extern const unsigned ember_nprogs;

typedef struct { int tick; unsigned char *b; size_t n; } input;
typedef struct { size_t step; int kind; char *text; unsigned char *b; size_t n; } event;
enum { EV_TX, EV_DROP, EV_NOTE };

static input *ins; static size_t nins, capins;
static event *evs; static size_t nevs, capevs;
static size_t pos, off, cur;
static unsigned char *frame; static size_t nframe, capframe;
static char header[512];
static jmp_buf trap_jmp;
static char trap_msg[512];

static void *grow(void *p, size_t *cap, size_t need, size_t elt) {
  if (need <= *cap) return p;
  size_t c = *cap ? *cap * 2 : 64;
  while (c < need) c *= 2;
  p = realloc(p, c * elt);
  if (!p) { perror("realloc"); exit(2); }
  *cap = c;
  return p;
}

static void push_event(int kind, char *text, unsigned char *b, size_t n) {
  evs = grow(evs, &capevs, nevs + 1, sizeof *evs);
  evs[nevs].step = cur; evs[nevs].kind = kind; evs[nevs].text = text;
  evs[nevs].b = b; evs[nevs].n = n;
  nevs++;
}

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static void read_inputs(const char *path) {
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); exit(2); }
  static char line[1 << 20];
  nins = 0; header[0] = 0;
  while (fgets(line, sizeof line, f)) {
    if (line[0] == '#') {
      if (strstr(line, "ember-trace") && !header[0]) {
        snprintf(header, sizeof header, "%.500s", line);
        header[strcspn(header, "\n")] = 0;
      }
      continue;
    }
    char kind[16];
    int consumed = 0;
    if (sscanf(line, "%*s %15s %n", kind, &consumed) < 1) continue;
    if (strcmp(kind, "tick") == 0) {
      ins = grow(ins, &capins, nins + 1, sizeof *ins);
      ins[nins].tick = 1; ins[nins].b = NULL; ins[nins].n = 0; nins++;
    } else if (strcmp(kind, "rx") == 0) {
      const char *p = line + consumed;
      size_t cap = strlen(p) / 2 + 1, n = 0;
      unsigned char *b = malloc(cap);
      for (;;) {
        while (*p == ' ') p++;
        if (*p == '#' || hexval(p[0]) < 0 || hexval(p[1]) < 0) break;
        b[n++] = (unsigned char)(hexval(p[0]) * 16 + hexval(p[1]));
        p += 2;
      }
      ins = grow(ins, &capins, nins + 1, sizeof *ins);
      ins[nins].tick = 0; ins[nins].b = b; ins[nins].n = n; nins++;
    }
  }
  fclose(f);
}

static const ember_prog *prog;

/* Not for a program that reads frame by frame: there the end of a chunk
 * is an item still to be read. */
static void normalize(void) {
  if (*prog->framed) return;
  while (pos < nins && !ins[pos].tick && off >= ins[pos].n) { pos++; off = 0; }
}

uint16_t ember_input_next(void) {
  normalize();
  if (pos >= nins) return 0xFFFFu;
  if (ins[pos].tick) { cur = pos; pos++; off = 0; normalize(); return 0x0100u; }
  uint16_t v = ins[pos].b[off];
  cur = pos; off++;
  normalize();
  return v;
}

uint16_t ember_ring_pop(void) { return ember_input_next(); }

uint16_t ember_input_frame(void) {
  if (pos >= nins) return 0xFFFFu;
  cur = pos;
  if (ins[pos].tick) { pos++; off = 0; return 0x0100u; }
  if (off < ins[pos].n) return ins[pos].b[off++];
  pos++; off = 0;
  return 0x0200u;
}

void ember_out_byte(uint8_t b) {
  frame = grow(frame, &capframe, nframe + 1, 1);
  frame[nframe++] = b;
}

void ember_out_end(void) {
  unsigned char *b = malloc(nframe ? nframe : 1);
  if (nframe) memcpy(b, frame, nframe);
  push_event(EV_TX, NULL, b, nframe);
  nframe = 0;
}

void ember_drop(uint8_t code) {
  if (EMBER_TRACE < 2) return;
  char *t = malloc(256);
  if (code < *prog->ndrops) snprintf(t, 256, "%s", prog->drops[code]);
  else snprintf(t, 256, "code-%u", (unsigned)code);
  push_event(EV_DROP, t, NULL, 0);
}

void ember_note(uint8_t code, uint32_t value) {
  if (EMBER_TRACE < 2) return;
  char *t = malloc(256);
  if (code < *prog->nnotes) snprintf(t, 256, "%s %lu", prog->notes[code], (unsigned long)value);
  else snprintf(t, 256, "note-%u %lu", (unsigned)code, (unsigned long)value);
  push_event(EV_NOTE, t, NULL, 0);
}

static uint32_t mmio_addr[64], mmio_val[64];
static unsigned nmmio;
uint32_t ember_mmio_read32(uint32_t a) {
  for (unsigned i = 0; i < nmmio; i++) if (mmio_addr[i] == a) return mmio_val[i];
  return 0;
}
void ember_mmio_write32(uint32_t a, uint32_t v) {
  for (unsigned i = 0; i < nmmio; i++) if (mmio_addr[i] == a) { mmio_val[i] = v; return; }
  if (nmmio < 64) { mmio_addr[nmmio] = a; mmio_val[nmmio] = v; nmmio++; }
}

void ember_trap(const char *where) {
  snprintf(trap_msg, sizeof trap_msg, "%s", where);
  longjmp(trap_jmp, 1);
}

static void print_line(FILE *o, size_t step, const char *kind, const char *rest) {
  char s[32];
  snprintf(s, sizeof s, "%zu", step);
  fprintf(o, "%-6s %-4s", s, kind);
  if (rest && rest[0]) fprintf(o, " %s", rest);
  fputc('\n', o);
}

static void print_hex_line(FILE *o, size_t step, const char *kind, const unsigned char *b, size_t n) {
  char s[32];
  snprintf(s, sizeof s, "%zu", step);
  if (n == 0) { fprintf(o, "%-6s %s\n", s, kind); return; }
  fprintf(o, "%-6s %-4s ", s, kind);
  for (size_t i = 0; i < n; i++) fprintf(o, i ? " %02x" : "%02x", b[i]);
  fputc('\n', o);
}

/* Returns 3 on a trap, 0 otherwise. */
static int run_one(unsigned k, const char *in_path, FILE *o) {
  if (k >= ember_nprogs) { fprintf(stderr, "no program %u\n", k); exit(2); }
  prog = &ember_progs[k];
  read_inputs(in_path);
  nevs = 0; pos = 0; off = 0; cur = 0; nframe = 0; nmmio = 0;
  int trapped = 0;
  if (setjmp(trap_jmp) == 0) {
    int idle = 0;
    for (;;) {
      normalize();
      if (pos >= nins || idle >= 3) break;
      size_t bp = pos, bo = off;
      prog->entry();
      idle = (pos == bp && off == bo) ? idle + 1 : 0;
    }
  } else {
    trapped = 1;
  }
  fprintf(o, "%s\n", header[0] ? header : "# ember-trace v1  impl=c  build=dev  profile=host64  link=slip");
  for (size_t i = 0; i < nins; i++) {
    if (ins[i].tick) print_line(o, i, "tick", NULL);
    else print_hex_line(o, i, "rx", ins[i].b, ins[i].n);
    for (size_t e = 0; e < nevs; e++) {
      if (evs[e].step != i) continue;
      if (evs[e].kind == EV_TX) print_hex_line(o, i, "tx", evs[e].b, evs[e].n);
      else if (evs[e].kind == EV_DROP) { char r[300]; snprintf(r, sizeof r, "reason=%s", evs[e].text); print_line(o, i, "drop", r); }
      else print_line(o, i, "note", evs[e].text);
    }
  }
  if (trapped) { char r[600]; snprintf(r, sizeof r, "trap %s", trap_msg); print_line(o, cur, "note", r); }
  for (size_t e = 0; e < nevs; e++) { free(evs[e].text); free(evs[e].b); }
  for (size_t i = 0; i < nins; i++) free(ins[i].b);
  return trapped ? 3 : 0;
}

int main(int argc, char **argv) {
  if (argc == 3 && strcmp(argv[1], "--batch") == 0) {
    FILE *l = fopen(argv[2], "r");
    if (!l) { perror(argv[2]); return 2; }
    unsigned k; char in[4096], out[4096];
    int status = 0;
    while (fscanf(l, "%u %4095s %4095s", &k, in, out) == 3) {
      fflush(NULL);
      pid_t pid = fork();
      if (pid < 0) { perror("fork"); return 2; }
      if (pid == 0) {
        FILE *o = fopen(out, "w");
        if (!o) { perror(out); _exit(2); }
        run_one(k, in, o);
        fclose(o);
        _exit(0);
      }
      int ws;
      waitpid(pid, &ws, 0);
      if (!WIFEXITED(ws) || WEXITSTATUS(ws) != 0) status = 1;
    }
    fclose(l);
    return status;
  }
  unsigned k = 0;
  int a = 1;
  if (argc >= 3 && strcmp(argv[1], "-p") == 0) { k = (unsigned)atoi(argv[2]); a = 3; }
  if (a >= argc) { fprintf(stderr, "usage: harness [-p K] inputs.trace | --batch LIST\n"); return 2; }
  return run_one(k, argv[a], stdout);
}
