(* file -- POSIX file I/O with linear type safety *)
(* Linear fd must be closed exactly once. Reads/writes through arrays. *)
(* Returns result/option types -- errors cannot be ignored. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use result as R

(* ============================================================
   C syscall wrappers (the entire unsafe surface)
   ============================================================ *)

$UNSAFE begin
%{#
#ifndef _FILE_RUNTIME_DEFINED
#define _FILE_RUNTIME_DEFINED
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <dirent.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

/* flags are file's own values (the O_* stadefs below); the host's
   O_* bits differ between systems (O_CREAT is 64 on Linux, 512 on
   macOS and the BSDs), so they are translated here. */
static int _file_open(const char *path, int flags, int mode) {
  int f;
  switch (flags & 3) {
    case 0: f = O_RDONLY; break;
    case 1: f = O_WRONLY; break;
    default: f = O_RDWR; break;
  }
  if (flags & 64) f |= O_CREAT;
  if (flags & 512) f |= O_TRUNC;
  if (flags & 1024) f |= O_APPEND;
  int fd = open(path, f, mode);
  return fd >= 0 ? fd : -errno;
}
/* Reads until len bytes or EOF; a failure before any byte is -errno,
   after some bytes those bytes: the next read reports it. EINTR is
   retried, as the readers of Rust do. */
static int _file_read(int fd, void *buf, int len) {
  int total = 0;
  while (total < len) {
    int n = (int)read(fd, (char *)buf + total, (unsigned int)(len - total));
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) return total > 0 ? total : -errno;
    if (n == 0) break;
    total += n;
  }
  return total;
}
/* Writes all len bytes (as Rust's write_all): len, or -errno of the
   write that failed. EINTR is retried. */
static int _file_write(int fd, const void *buf, int len) {
  int total = 0;
  while (total < len) {
    int n = (int)write(fd, (const char *)buf + total, (unsigned int)(len - total));
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) return -errno;
    if (n == 0) return -EIO;
    total += n;
  }
  return total;
}
static int _file_close(int fd) {
  return close(fd);
}
/* A size that does not fit an int is EFBIG, not a truncated value. */
static int _file_size_of(const struct stat *st) {
  if (st->st_size < 0 || st->st_size > 2147483647) return -EFBIG;
  return (int)st->st_size;
}
static int _file_stat_size(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return -errno;
  return _file_size_of(&st);
}
static int _file_fd_size(int fd) {
  struct stat st;
  if (fstat(fd, &st) != 0) return -errno;
  return _file_size_of(&st);
}
static void *_file_opendir(const char *path) {
  return (void *)opendir(path);
}
static int _file_closedir(void *dirp) {
  return closedir(dirp);
}
/* All of a directory's entries, read in one pass and sorted by name
   (bytewise, a prefix before its extensions), so walks over them are
   bounded and in the same order on every system. */
typedef struct { char *name; int len; } _file_entry_t;
typedef struct { int n; _file_entry_t *es; } _file_entries_t;
static int _file_entry_cmp(const void *x, const void *y) {
  const _file_entry_t *a = (const _file_entry_t *)x;
  const _file_entry_t *b = (const _file_entry_t *)y;
  int m = a->len < b->len ? a->len : b->len;
  int c = memcmp(a->name, b->name, m);
  if (c != 0) return c;
  return a->len - b->len;
}
static void *_file_dir_read(const char *path) {
  DIR *d = opendir(path);
  _file_entries_t *r;
  struct dirent *e;
  int cap = 16;
  if (!d) return (void *)0;
  r = (_file_entries_t *)malloc(sizeof(_file_entries_t));
  r->n = 0;
  r->es = (_file_entry_t *)malloc(cap * sizeof(_file_entry_t));
  while ((e = readdir(d)) != 0) {
    int len = (int)strlen(e->d_name);
    char *s = (char *)malloc(len > 0 ? len : 1);
    if (r->n == cap) {
      cap = 2 * cap;
      r->es = (_file_entry_t *)realloc(r->es, cap * sizeof(_file_entry_t));
    }
    memcpy(s, e->d_name, len);
    r->es[r->n].name = s;
    r->es[r->n].len = len;
    r->n++;
  }
  closedir(d);
  qsort(r->es, r->n, sizeof(_file_entry_t), _file_entry_cmp);
  return (void *)r;
}
static int _file_entries_count(void *p) {
  return ((_file_entries_t *)p)->n;
}
static int _file_entries_name(void *p, int i, char *name_buf, int max_len) {
  _file_entry_t *e = &((_file_entries_t *)p)->es[i];
  int len = e->len;
  if (len > max_len) len = max_len;
  memcpy(name_buf, e->name, len);
  return len;
}
static void _file_entries_free(void *p) {
  _file_entries_t *r = (_file_entries_t *)p;
  int i;
  for (i = 0; i < r->n; i++) free(r->es[i].name);
  free(r->es);
  free(r);
}
static int _file_ptr_nonnull(void *p) {
  return p != (void*)0 ? 1 : 0;
}
static int _file_chdir(const char *path) {
  return chdir(path);
}
static long _file_mtime(const char *path) {
  struct stat st;
  if (stat(path, &st) == 0) return (long)st.st_mtime;
  return -1;
}
static int _file_exists(const char *path) {
  struct stat st;
  return stat(path, &st) == 0 ? 1 : 0;
}
/* The permission bits (st_mode & 07777) of path; -errno on failure. */
static int _file_mode(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return -errno;
  return (int)(st.st_mode & 07777);
}
/* 0, or -errno on failure. */
static int _file_chmod(const char *path, int mode) {
  return chmod(path, (mode_t)mode) == 0 ? 0 : -errno;
}
static int _file_mkdir(const char *path, int mode) {
  return mkdir(path, mode);
}
#endif
%}
end

(* ============================================================
   Open flags
   ============================================================ *)

(* Portable values for file_open's flags, combined with +: the access
   mode (one of the first three) plus any of the rest. file_open
   translates them to the host's open(2) flags. Other bits are ignored. *)

#pub stadef O_RDONLY = 0
#pub stadef O_WRONLY = 1
#pub stadef O_RDWR = 2
#pub stadef O_CREAT = 64
#pub stadef O_TRUNC = 512
#pub stadef O_APPEND = 1024

(* ============================================================
   Linear file descriptor
   ============================================================ *)

#pub datavtype fd =
  | fd_mk of (int)

(* ============================================================
   Linear directory handle
   ============================================================ *)

#pub datavtype dir =
  | dir_mk of (ptr)

(* A directory's entries, read in one pass and sorted by name (bytewise):
   n names, so a walk over them is bounded by n. *)
#pub datavtype entries(int) =
  | {n:nat} entries_mk(n) of (ptr, int n)

(* ============================================================
   File operations
   ============================================================ *)

(* The open file, or the errno (> 0) of why it could not be opened,
   as Rust's io::Error carries it. *)
#pub fn file_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n,
   flags: int, mode: int): $R.result(fd, int)

(* Bytes read into buf[0, k), at most len (read(2)'s contract), or
   the errno (> 0) of a read that failed before any byte. *)
#pub fn file_read
  {l:agz}{n:pos}
  (f: !fd, buf: !$A.arr(byte, l, n), len: int n): $R.result([k:nat | k <= n] int k, int)

(* Writes all n bytes of buf, retrying short writes (as Rust's
   write_all), or fails with the errno (> 0) of the write that failed. *)
#pub fn file_write
  {lb:agz}{n:pos}
  (f: !fd, buf: !$A.borrow(byte, lb, n), len: int n): $R.result(int n, int)

#pub fn file_close(f: fd): $R.result(int, int)

(* Size in bytes of the file at path, or the errno (> 0): EFBIG for a
   size that does not fit an int. *)
#pub fn file_size
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([s:nat] int s, int)

(* Size in bytes of the open file f, as file_size *)
#pub fn fd_size(f: !fd): $R.result([s:nat] int s, int)

(* Copies the bytes of src, from its position to the size it has when
   the copy starts (fd_size), to dst; the number copied (less when src
   ends early), or the errno (> 0) of a failed read or write. *)
#pub fn fd_copy(src: !fd, dst: !fd): $R.result([c:nat] int c, int)

(* ============================================================
   Directory operations
   ============================================================ *)

#pub fn dir_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(dir, int)

#pub fn dir_close(d: dir): $R.result(int, int)

(* Every entry of the directory at path (including . and ..), sorted by
   name. *)
#pub fn dir_read
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([k:nat] entries(k), int)

#pub fn entries_count {n:int} (es: !entries(n)): int n

(* Length of entry i's name, copied to name_buf[0, k) and truncated to
   max_len. *)
#pub fn entries_name
  {n:int}{i:nat | i < n}{l:agz}{m:pos}
  (es: !entries(n), i: int i, name_buf: !$A.arr(byte, l, m), max_len: int m): [k:nat | k <= m] int k

#pub fn entries_free {n:int} (es: entries(n)): void

(* ============================================================
   Extra POSIX operations
   ============================================================ *)

#pub fn file_chdir
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, int)

#pub fn file_mtime
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, int)

#pub fn file_exists
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): bool

#pub fn file_mkdir
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int): $R.result(int, int)

(* The permission bits (0 to 07777) of the file at path; the errno
   (positive) when it cannot be read. *)
#pub fn file_mode
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([m:nat | m <= 4095] int m, int)

(* Sets the permission bits of the file at path to mode; the errno
   (positive) when it cannot. *)
#pub fn file_chmod
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int): $R.result(int, int)

(* ============================================================
   Buffered reader
   ============================================================ *)

#pub stadef BUF_SIZE = 4096

(* filled bytes of the buffer are valid; pos <= filled is the next one
   to hand out. Both bounds are in the type, so no access is checked at
   runtime. *)
#pub datavtype buf_reader =
  | {lb:agz}{f,p:nat | p <= f; f <= BUF_SIZE}
    buf_reader_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int f, int p)

#pub fn buf_reader_create(f: fd): buf_reader

#pub fun buf_read
  {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), len: int n): $R.option(int)

#pub fun buf_read_line
  {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), max_len: int n): $R.option(int)

#pub fn buf_reader_close(r: buf_reader): $R.result(int, int)

(* ============================================================
   Buffered writer
   ============================================================ *)

(* pos <= BUF_SIZE bytes are pending. *)
#pub datavtype buf_writer =
  | {lb:agz}{p:nat | p <= BUF_SIZE}
    buf_writer_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int p)

#pub fn buf_writer_create(f: fd): buf_writer

#pub fn buf_write
  {lb:agz}{n:pos}
  (w: !buf_writer, data: !$A.borrow(byte, lb, n), len: int n): $R.result(int, int)

#pub fn buf_write_byte(w: !buf_writer, b: int): $R.result(int, int)

#pub fn buf_flush(w: !buf_writer): $R.result(int, int)

#pub fn buf_writer_close(w: buf_writer): $R.result(int, int)

(* ============================================================
   Internal helpers
   ============================================================ *)

fn _with_cpath
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): [lc:agz] $A.arr(byte, lc, n+1) = let
  val cpath = $A.alloc<byte>(path_len + 1)
  val () = $A.write_borrow(cpath, 0, path, path_len)
  val () = $A.write_byte(cpath, path_len, 0)
in cpath end

(* ============================================================
   File implementations
   ============================================================ *)

implement file_open {lb}{n} (path, path_len, flags, mode) = let
  val cpath = _with_cpath(path, path_len)
  val rawfd = $UNSAFE begin $extfcall(int, "_file_open",
    $UNSAFE.castvwtp1{ptr}(cpath), flags, mode) end
  val () = $A.free<byte>(cpath)
in
  if rawfd >= 0 then $R.ok(fd_mk(rawfd))
  else $R.err(~rawfd)
end

implement file_read {l}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall([k:int | k <= n] int k, "_file_read", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), len) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(~r)
end

implement file_write {lb}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  (* _file_write returns len or -errno *)
  val r = $UNSAFE begin $extfcall([k:int | k == n || k < 0] int k, "_file_write", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), len) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(~r)
end

implement file_close(f) = let
  val+ ~fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall(int, "_file_close", rawfd) end
in
  if $AR.eq_int_int(r, 0) then $R.ok(0)
  else $R.err(r)
end

implement file_size {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val sz = $UNSAFE begin $extfcall([s:int] int s, "_file_stat_size",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(~sz)
end

implement fd_size(f) = let
  val+ @fd_mk(rawfd) = f
  val sz = $UNSAFE begin $extfcall([s:int] int s, "_file_fd_size", rawfd) end
  prval () = fold@(f)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(~sz)
end

(* 64 KiB at a time, until r bytes remain to copy. A chunk read past the
   size (the file grew) is copied only up to it; a read of 0 bytes is
   the end of src. *)
implement fd_copy(src, dst) = let
  fun loop {l:agz}{r,c:nat} .<r>.
    (src: !fd, dst: !fd, buf: $A.arr(byte, l, 65536), r: int r, c: int c)
    : @($R.result([c:nat] int c, int), $A.arr(byte, l, 65536)) =
    if r <= 0 then @($R.ok(c), buf)
    else (case+ file_read(src, buf, 65536) of
      | ~$R.err(e) => @($R.err(e), buf)
      | ~$R.ok(k) => let
          val k = (if k > r then r else k): [k2:nat | k2 <= r; k2 <= 65536] int k2
        in
          if k <= 0 then @($R.ok(c), buf)
          else let
            val @(fz, bv) = $A.freeze<byte>(buf)
            val @(left, right) = $A.borrow_split<byte>(fz, bv, k)
            val w = file_write(dst, left, k)
            val () = $A.drop<byte>(fz, $A.borrow_join<byte>(fz, left, right))
            val buf = $A.thaw<byte>(fz)
          in
            case+ w of
            | ~$R.ok(_) => loop(src, dst, buf, r - k, c + k)
            | ~$R.err(e) => @($R.err(e), buf)
          end
        end)
in
  case+ fd_size(src) of
  | ~$R.err(e) => $R.err(e)
  | ~$R.ok(s) => let
      val @(res, buf) = loop(src, dst, $A.alloc<byte>(65536), s, 0)
      val () = $A.free<byte>(buf)
    in res end
end

(* ============================================================
   Directory implementations
   ============================================================ *)

implement dir_open {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val dp = $UNSAFE begin $extfcall(ptr, "_file_opendir",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
  val nonnull = $UNSAFE begin $extfcall(int, "_file_ptr_nonnull", dp) end
in
  if nonnull > 0 then $R.ok(dir_mk(dp))
  else $R.err(~1)
end

implement dir_read {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val p = $UNSAFE begin $extfcall(ptr, "_file_dir_read",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if ptr_isnot_null(p) then let
    val k = $UNSAFE begin $extfcall([k:nat] int k, "_file_entries_count", p) end
  in $R.ok(entries_mk(p, k)) end
  else $R.err(~1)
end

implement entries_count {n} (es) = let
  val+ @entries_mk(_, k) = es
  val r = k
  prval () = fold@(es)
in r end

implement entries_name {n}{i}{l}{m} (es, i, name_buf, max_len) = let
  val+ @entries_mk(p, _) = es
  val r = $UNSAFE begin $extfcall([k:nat | k <= m] int k, "_file_entries_name", p, i,
    $UNSAFE.castvwtp1{ptr}(name_buf), max_len) end
  prval () = fold@(es)
in r end

implement entries_free {n} (es) = let
  val+ ~entries_mk(p, _) = es
in $UNSAFE begin $extfcall(void, "_file_entries_free", p) end end

implement dir_close(d) = let
  val+ ~dir_mk(dp) = d
  val nonnull = $UNSAFE begin $extfcall(int, "_file_ptr_nonnull", dp) end
  val r = if nonnull > 0 then $UNSAFE begin $extfcall(int, "_file_closedir", dp) end else ~1
in
  if $AR.eq_int_int(r, 0) then $R.ok(0)
  else $R.err(r)
end

(* ============================================================
   Extra POSIX operation implementations
   ============================================================ *)

implement file_chdir {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_chdir",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if $AR.eq_int_int(r, 0) then $R.ok(0)
  else $R.err(r)
end

implement file_mtime {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val mt = $UNSAFE begin $extfcall(int, "_file_mtime",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if mt >= 0 then $R.ok(mt)
  else $R.err(~1)
end

implement file_exists {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_exists",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in r > 0 end

implement file_mode {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val m = $UNSAFE begin $extfcall([m:int | m <= 4095] int m, "_file_mode",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if m >= 0 then $R.ok(m)
  else $R.err(~m)
end

implement file_chmod {lb}{n} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_chmod",
    $UNSAFE.castvwtp1{ptr}(cpath), mode) end
  val () = $A.free<byte>(cpath)
in
  if $AR.eq_int_int(r, 0) then $R.ok(0)
  else $R.err(~r)
end

implement file_mkdir {lb}{n} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_mkdir",
    $UNSAFE.castvwtp1{ptr}(cpath), mode) end
  val () = $A.free<byte>(cpath)
in
  if $AR.eq_int_int(r, 0) then $R.ok(0)
  else $R.err(r)
end

(* ============================================================
   Buffered reader implementations
   ============================================================ *)

implement buf_reader_create(f) = let
  val buf = $A.alloc<byte>(4096)
in buf_reader_mk(f, buf, 0, 0) end

(* dst[0..c) := src[p..p+c). *)
fun _copy_out {ld,ls:agz}{n:pos}{p,c:nat | p + c <= BUF_SIZE; c <= n}{k:nat | k <= c} .<c - k>.
  (dst: !$A.arr(byte, ld, n), src: !$A.arr(byte, ls, BUF_SIZE),
   p: int p, k: int k, c: int c): void =
  if k >= c then ()
  else let
    val () = $A.set<byte>(dst, k, $A.get<byte>(src, p + k))
  in _copy_out(dst, src, p, k + 1, c) end

(* Refill the buffer from the file. read(2) returns at most the count
   asked for; that contract is stated in the FFI result type, which is
   where this unsafe package vouches for its C code. *)
fn _buf_refill(r: !buf_reader): int = let
  val+ @buf_reader_mk(f, buf, filled, pos) = r
  val+ @fd_mk(rawfd) = f
  val n = $UNSAFE begin $extfcall([k:int | k <= BUF_SIZE] int k, "_file_read", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), 4096) end
  prval () = fold@(f)
  val nf = (if n > 0 then n else 0): [k:nat | k <= BUF_SIZE] int k
  val () = filled := nf
  val () = pos := 0
  prval () = fold@(r)
in n end

(* Hand out up to len available bytes; none when nothing is buffered. *)
fn _buf_take {l:agz}{n:pos}
  (r: !buf_reader, dst: !$A.arr(byte, l, n), len: int n): $R.option(int) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = r
  val avail = filled - pos
in
  if avail <= 0 then let
    prval () = fold@(r)
  in $R.none() end
  else let
    val to_copy = min(avail, len)
    val () = _copy_out(dst, ibuf, pos, 0, to_copy)
    val () = pos := pos + to_copy
    prval () = fold@(r)
  in $R.some(to_copy) end
end

implement buf_read {l}{n} (r, dst, len) = let
  val first = _buf_take(r, dst, len)
in
  case+ first of
  | ~$R.some(k) => $R.some(k)
  | ~$R.none() => let
      val n = _buf_refill(r)
    in
      if n > 0 then _buf_take(r, dst, len) else $R.none()
    end
end

(* Index of the first newline in buf[i..lim), or ~1. *)
fun _scan_nl {lb:agz}{i,lim:nat | i <= lim; lim <= BUF_SIZE} .<lim - i>.
  (ibuf: !$A.arr(byte, lb, BUF_SIZE), i: int i, lim: int lim)
  : [r:int | r == ~1 || (i <= r && r < lim)] int r =
  if i >= lim then ~1
  else if byte2int0($A.get<byte>(ibuf, i)) = 10 then i
  else _scan_nl(ibuf, i + 1, lim)

(* One line (without the newline) from the buffered bytes, truncated to
   max_len; none when nothing is buffered. Without a newline, the rest of
   the buffer is returned. *)
fn _buf_line {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), max_len: int n): $R.option(int) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = r
in
  if pos >= filled then let
    prval () = fold@(r)
  in $R.none() end
  else let
    val nl = _scan_nl(ibuf, pos, filled)
  in
    if nl >= 0 then let
      val line_len = nl - pos
      val copy_len = min(line_len, max_len)
      val () = _copy_out(buf, ibuf, pos, 0, copy_len)
      val () = pos := nl + 1
      prval () = fold@(r)
    in $R.some(copy_len) end
    else let
      val rest = filled - pos
      val copy_len = min(rest, max_len)
      val () = _copy_out(buf, ibuf, pos, 0, copy_len)
      val () = pos := filled
      prval () = fold@(r)
    in $R.some(copy_len) end
  end
end

implement buf_read_line {l}{n} (r, buf, max_len) = let
  val first = _buf_line(r, buf, max_len)
in
  case+ first of
  | ~$R.some(k) => $R.some(k)
  | ~$R.none() => let
      val n = _buf_refill(r)
    in
      if n > 0 then _buf_line(r, buf, max_len) else $R.none()
    end
end

implement buf_reader_close(r) = let
  val+ ~buf_reader_mk(f, buf, _, _) = r
  val () = $A.free<byte>(buf)
in file_close(f) end

(* ============================================================
   Buffered writer implementations
   ============================================================ *)

implement buf_writer_create(f) = let
  val buf = $A.alloc<byte>(4096)
in buf_writer_mk(f, buf, 0) end

fn _buf_do_flush(w: !buf_writer): $R.result(int, int) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos <= 0 then let
    prval () = fold@(w)
  in $R.ok(0) end
  else let
    val @(fz, bv) = $A.freeze<byte>(buf)
    val+ @fd_mk(rawfd) = f
    val written = $UNSAFE begin $extfcall(int, "_file_write", rawfd,
      $UNSAFE.castvwtp1{ptr}(bv), pos) end
    prval () = fold@(f)
    val () = $A.drop<byte>(fz, bv)
    val buf2 = $A.thaw<byte>(fz)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in
    if written >= 0 then $R.ok(written)
    else $R.err(~written)
  end
end

implement buf_flush(w) = _buf_do_flush(w)

(* A full buffer is flushed before the byte is stored; the byte is the
   low 8 bits of b, as before, now without a cast. *)
implement buf_write_byte(w, b) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos < 4096 then let
    val () = $A.set<byte>(buf, pos, $A.int2byte($AR.low_byte(b)))
    val () = pos := pos + 1
    val full = (pos >= 4096)
    prval () = fold@(w)
  in
    if full then _buf_do_flush(w) else $R.ok(1)
  end
  else let
    prval () = fold@(w)
    val r = _buf_do_flush(w)
  in
    case+ r of
    | ~$R.ok(_) => buf_write_byte(w, b)
    | ~$R.err(e) => $R.err(e)
  end
end

(* buf[p..p+c) := src[0..c). *)
fun _copy_in {ld,ls:agz}{n:pos}{p,c:nat | p + c <= BUF_SIZE; c <= n}{k:nat | k <= c} .<c - k>.
  (dst: !$A.arr(byte, ld, BUF_SIZE), src: !$A.borrow(byte, ls, n),
   p: int p, k: int k, c: int c): void =
  if k >= c then ()
  else let
    val () = $A.set<byte>(dst, p + k, $A.read<byte>(src, k))
  in _copy_in(dst, src, p, k + 1, c) end

(* After a flush: buffer the data if it now fits, otherwise (it is larger
   than the buffer) write it straight to the file. No recursion. *)
fn _buf_write_flushed {lb:agz}{n:pos}
  (w: !buf_writer, data: !$A.borrow(byte, lb, n), len: int n): $R.result(int, int) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos + len <= 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val () = pos := pos + len
    val full = (pos >= 4096)
    prval () = fold@(w)
  in
    if full then _buf_do_flush(w) else $R.ok(len)
  end
  else let
    val r = file_write(f, data, len)
    prval () = fold@(w)
  in
    case+ r of
    | ~$R.ok(k) => $R.ok(k)
    | ~$R.err(e) => $R.err(e)
  end
end

implement buf_write {lb}{n} (w, data, len) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos + len <= 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val () = pos := pos + len
    val full = (pos >= 4096)
    prval () = fold@(w)
  in
    if full then _buf_do_flush(w) else $R.ok(len)
  end
  else let
    prval () = fold@(w)
    val r = _buf_do_flush(w)
  in
    case+ r of
    | ~$R.ok(_) => _buf_write_flushed(w, data, len)
    | ~$R.err(e) => $R.err(e)
  end
end

implement buf_writer_close(w) = let
  val flush_r = _buf_do_flush(w)
  val () = $R.discard<int><int>(flush_r)
  val+ ~buf_writer_mk(f, buf, _) = w
  val () = $A.free<byte>(buf)
in file_close(f) end
