#!/bin/sh
# Compiles file's C runtime on its own (no bats, no ATS2) and checks
# _file_dir_read when memory runs out: each of its allocations fails in
# turn, and each time it must return null having freed everything it
# allocated. It runs on every OS in CI, including ones where bats cannot
# run yet.
#
# usage: tests/c/run.sh   (needs cc)
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
sed -n '/^%{#$/,/^%}$/p' "$ROOT/src/lib.bats" | sed '1d;$d' > "$TMP/file_runtime.h"
cat > "$TMP/main.c" <<'C'
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <dirent.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>
#include <stdio.h>
/* The runtime's allocations go through these: the fail_at-th one fails
   (counting from 0), and live counts the blocks not yet freed. */
static int calls, fail_at = -1, live;
static void *t_malloc(size_t n) {
  void *p;
  if (calls++ == fail_at) return NULL;
  p = malloc(n);
  if (p) live++;
  return p;
}
static void *t_realloc(void *q, size_t n) {
  void *p;
  if (calls++ == fail_at) return NULL;
  p = realloc(q, n);
  if (p && !q) live++;
  return p;
}
static void t_free(void *p) {
  if (p) live--;
  free(p);
}
#define malloc t_malloc
#define realloc t_realloc
#define free t_free
#include "file_runtime.h"
#undef malloc
#undef realloc
#undef free
int main(int argc, char **argv) {
  const char *dir = argv[1];
  int want = atoi(argv[2]), total, i;
  void *r;
  /* Every allocation succeeds: the number made, and the entries. */
  calls = 0; fail_at = -1; live = 0;
  r = _file_dir_read(dir);
  if (!r || _file_entries_count(r) != want) {
    printf("FAIL c-dir-read: %d entries, want %d\n", r ? _file_entries_count(r) : -1, want);
    return 1;
  }
  _file_entries_free(r);
  total = calls;
  if (live != 0) { printf("FAIL c-dir-read: %d blocks lost\n", live); return 1; }
  /* The entries outgrow the first array, so it is reallocated too. */
  if (total < want + 3) { printf("FAIL c-dir-read: only %d allocations\n", total); return 1; }
  for (i = 0; i < total; i++) {
    calls = 0; fail_at = i; live = 0;
    r = _file_dir_read(dir);
    if (r) { printf("FAIL c-dir-oom: allocation %d failed, got entries\n", i); return 1; }
    if (live != 0) { printf("FAIL c-dir-oom: allocation %d failed, %d blocks lost\n", i, live); return 1; }
  }
  printf("ok   c-dir-read\n");
  printf("ok   c-dir-oom (%d allocations failed in turn)\n", total);
  return 0;
}
C
cc -Wall -Wno-unused-function -o "$TMP/t" "$TMP/main.c"
mkdir "$TMP/d"
i=0
while [ $i -lt 40 ]; do : > "$TMP/d/f$i"; i=$((i + 1)); done
# 40 files plus . and ..
"$TMP/t" "$TMP/d" 42
