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
#include <limits.h>

/* file's own code for an errno (io_error's, decoded once by _io_error
   below): errno's numbers differ between systems (EAGAIN is 11 on Linux
   and 35 on macOS), so they are named here, by their macros. */
static int _file_error_code(int e) {
  switch (e) {
    case ENOENT: return 1;
    case EACCES: case EPERM: return 2;
    case EEXIST: return 3;
    case ENOTDIR: return 4;
    case EISDIR: return 5;
    case ENOTEMPTY: return 6;
    case EROFS: return 7;
    case ELOOP: return 8;
    case ENAMETOOLONG: return 9;
    case EINVAL: return 10;
    case EFBIG: case EOVERFLOW: return 11;
    case ENOSPC:
#ifdef EDQUOT
    case EDQUOT:
#endif
      return 12;
    case EMFILE: case ENFILE: return 13;
    case ENOMEM: return 14;
    case EBUSY: case ETXTBSY: return 15;
    case EPIPE: return 16;
    case EAGAIN:
#if defined(EWOULDBLOCK) && EWOULDBLOCK != EAGAIN
    case EWOULDBLOCK:
#endif
      return 17;
    case EBADF: return 18;
    case EIO: return 19;
    case ENOTSUP:
#if defined(EOPNOTSUPP) && EOPNOTSUPP != ENOTSUP
    case EOPNOTSUPP:
#endif
      return 20;
    case EXDEV: return 21;
    default: return 22;
  }
}
/* The failure errno names, as a negative result */
static int _file_failed(int e) {
  return -_file_error_code(e);
}
/* access and opening are file's own codes, encoded once by
   _access_code and _opening_code below; the host's O_* bits differ
   between systems (O_CREAT is 64 on Linux, 512 on macOS and the BSDs),
   so they are translated here. */
static int _file_open(const char *path, int access, int opening, int mode) {
  int f;
  int fd;
  switch (access) {
    case 0: f = O_RDONLY; break;
    case 1: f = O_WRONLY; break;
    default: f = O_RDWR; break;
  }
  switch (opening) {
    case 0: break;
    case 1: f |= O_CREAT; break;
    case 2: f |= O_CREAT | O_TRUNC; break;
    case 3: f |= O_CREAT | O_APPEND; break;
    case 4: f |= O_TRUNC; break;
    default: f |= O_APPEND; break;
  }
  fd = open(path, f, mode);
  return fd >= 0 ? fd : _file_failed(errno);
}
/* Reads until len bytes or EOF; a failure before any byte is -errno,
   after some bytes those bytes: the next read reports it. EINTR is
   retried, as the readers of Rust do. */
static int _file_read(int fd, void *buf, int len) {
  int total = 0;
  while (total < len) {
    int n = (int)read(fd, (char *)buf + total, (unsigned int)(len - total));
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) return total > 0 ? total : _file_failed(errno);
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
    if (n < 0) return _file_failed(errno);
    if (n == 0) return _file_failed(EIO);
    total += n;
  }
  return total;
}
static int _file_close(int fd) {
  return close(fd) == 0 ? 0 : _file_failed(errno);
}
/* A size that does not fit an int is EFBIG, not a truncated value. */
static int _file_size_of(const struct stat *st) {
  if (st->st_size < 0 || st->st_size > 2147483647) return _file_failed(EFBIG);
  return (int)st->st_size;
}
static int _file_stat_size(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return _file_failed(errno);
  return _file_size_of(&st);
}
static int _file_fd_size(int fd) {
  struct stat st;
  if (fstat(fd, &st) != 0) return _file_failed(errno);
  return _file_size_of(&st);
}
/* The code of the last failure of a call that returns a pointer (null
   when it fails): opendir and dir_read */
static int _file_last_failure = 0;
static int _file_last_failed(void) {
  return -_file_last_failure;
}
static void *_file_opendir(const char *path) {
  void *d = (void *)opendir(path);
  if (!d) _file_last_failure = _file_error_code(errno);
  return d;
}
static int _file_closedir(void *dirp) {
  return closedir(dirp) == 0 ? 0 : _file_failed(errno);
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
static void _file_entries_free(void *p);
/* Null when the directory cannot be opened or read, or when memory for
   its entries cannot be had (_file_last_failure says which); everything
   allocated so far is freed. */
static void *_file_dir_read(const char *path) {
  DIR *d = opendir(path);
  _file_entries_t *r;
  struct dirent *e;
  int cap = 16;
  if (!d) { _file_last_failure = _file_error_code(errno); return (void *)0; }
  _file_last_failure = _file_error_code(ENOMEM);
  r = (_file_entries_t *)malloc(sizeof(_file_entries_t));
  if (!r) { closedir(d); return (void *)0; }
  r->n = 0;
  r->es = (_file_entry_t *)malloc((size_t)cap * sizeof(_file_entry_t));
  if (!r->es) { free(r); closedir(d); return (void *)0; }
  for (;;) {
    int len;
    char *s;
    errno = 0;
    e = readdir(d);
    if (!e) break;
    if (r->n == cap) {
      _file_entry_t *es;
      if ((size_t)cap > ((size_t)INT_MAX / 2) / sizeof(_file_entry_t)) goto fail;
      es = (_file_entry_t *)realloc(r->es, 2 * (size_t)cap * sizeof(_file_entry_t));
      if (!es) goto fail;
      r->es = es;
      cap = 2 * cap;
    }
    len = (int)strlen(e->d_name);
    s = (char *)malloc(len > 0 ? (size_t)len : 1);
    if (!s) goto fail;
    memcpy(s, e->d_name, (size_t)len);
    r->es[r->n].name = s;
    r->es[r->n].len = len;
    r->n++;
  }
  /* readdir returns null at the end and on an error, which sets errno. */
  if (errno != 0) { _file_last_failure = _file_error_code(errno); goto fail; }
  closedir(d);
  qsort(r->es, (size_t)r->n, sizeof(_file_entry_t), _file_entry_cmp);
  return (void *)r;
fail:
  closedir(d);
  _file_entries_free(r);
  return (void *)0;
}
static int _file_entries_count(void *p) {
  return ((_file_entries_t *)p)->n;
}
/* A name is NUL-terminated inside d_name, so strlen(d_name) is less
   than sizeof(d_name), which is at most ENTRY_NAME_MAX (1024) on every
   host we build for (Linux and the BSDs 256, NetBSD 512, macOS 1024);
   a host with a larger or flexible d_name fails to compile here.
   entries_name's buffer holds ENTRY_NAME_MAX bytes, so a name always
   fits. */
_Static_assert(sizeof(((struct dirent *)0)->d_name) <= 1024,
  "d_name must fit ENTRY_NAME_MAX");
static int _file_entries_name(void *p, int i, char *name_buf) {
  _file_entry_t *e = &((_file_entries_t *)p)->es[i];
  memcpy(name_buf, e->name, e->len);
  return e->len;
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
  return chdir(path) == 0 ? 0 : _file_failed(errno);
}
/* 0, with the modification time (seconds since 1970, which may be
   before it) in *mtime, or the failure */
static int _file_mtime(const char *path, int *mtime) {
  struct stat st;
  if (stat(path, &st) != 0) return _file_failed(errno);
  if (st.st_mtime > 2147483647 || st.st_mtime < -2147483647 - 1) return _file_failed(EOVERFLOW);
  *mtime = (int)st.st_mtime;
  return 0;
}
static int _file_exists(const char *path) {
  struct stat st;
  return stat(path, &st) == 0 ? 1 : 0;
}
/* The permission bits (st_mode & 07777) of path, or the failure. */
static int _file_mode(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return _file_failed(errno);
  return (int)(st.st_mode & 07777);
}
/* 0, or the failure. */
static int _file_chmod(const char *path, int mode) {
  return chmod(path, (mode_t)mode) == 0 ? 0 : _file_failed(errno);
}
static int _file_mkdir(const char *path, int mode) {
  return mkdir(path, mode) == 0 ? 0 : _file_failed(errno);
}
#endif
%}
end

(* ============================================================
   How a file is opened, and why an operation failed
   ============================================================ *)

(* What a file is opened for *)
#pub datatype access =
  | ReadOnly
  | WriteOnly
  | ReadWrite

(* What opening does when the file is missing or has bytes: open it as
   it is (it must exist); create it when missing; create it when missing
   and empty it when not; create it when missing and write at its end;
   empty it (it must exist); write at its end (it must exist) *)
#pub datatype opening =
  | OpenExisting
  | CreateOrOpen
  | CreateOrTruncate
  | CreateOrAppend
  | TruncateExisting
  | AppendExisting

(* Why an operation failed: the kinds of errno, named as Rust's
   io::ErrorKind names them (an errno is a different number on each
   system, so it is not kept). Unrecognized is any other errno. *)
#pub datatype io_error =
  | NotFound            (* ENOENT *)
  | PermissionDenied    (* EACCES, EPERM *)
  | AlreadyExists       (* EEXIST *)
  | NotADirectory       (* ENOTDIR *)
  | IsADirectory        (* EISDIR *)
  | DirectoryNotEmpty   (* ENOTEMPTY *)
  | ReadOnlyFilesystem  (* EROFS *)
  | FilesystemLoop      (* ELOOP *)
  | InvalidFilename     (* ENAMETOOLONG *)
  | InvalidInput        (* EINVAL *)
  | FileTooLarge        (* EFBIG, EOVERFLOW: a size or time past an int *)
  | StorageFull         (* ENOSPC, EDQUOT *)
  | TooManyOpenFiles    (* EMFILE, ENFILE *)
  | OutOfMemory         (* ENOMEM *)
  | ResourceBusy        (* EBUSY, ETXTBSY *)
  | BrokenPipe          (* EPIPE *)
  | WouldBlock          (* EAGAIN *)
  | BadDescriptor       (* EBADF *)
  | DeviceError         (* EIO *)
  | Unsupported         (* ENOTSUP *)
  | CrossesDevices      (* EXDEV *)
  | Unrecognized        (* any other errno *)

(* What the error says, in words, for a message *)
#pub fn io_error_text (e: io_error): string

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

(* The open file, or why it could not be opened. mode is the
   permission bits of a file it creates. *)
#pub fn file_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n,
   access: access, opening: opening, mode: int): $R.result(fd, io_error)

(* Bytes read into buf[0, k), at most len (read(2)'s contract), or
   why a read failed before any byte. *)
#pub fn file_read
  {l:agz}{n:pos}{o:addr}
  (f: !fd, buf: !$A.arrx(byte, l, n, o), len: int n): $R.result([k:nat | k <= n] int k, io_error)

(* Writes all n bytes of buf, retrying short writes (as Rust's
   write_all), or fails with why the write that failed did. *)
#pub fn file_write
  {lb:agz}{n:pos}
  (f: !fd, buf: !$A.borrow(byte, lb, n), len: int n): $R.result(int n, io_error)

#pub fn file_close(f: fd): $R.result(int, io_error)

(* Size in bytes of the file at path, or why it cannot be had:
   FileTooLarge for a size that does not fit an int. *)
#pub fn file_size
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([s:nat] int s, io_error)

(* Size in bytes of the open file f, as file_size *)
#pub fn fd_size(f: !fd): $R.result([s:nat] int s, io_error)

(* Copies the bytes of src, from its position to the size it has when
   the copy starts (fd_size), to dst; the number copied (less when src
   ends early), or why a read or write failed. *)
#pub fn fd_copy(src: !fd, dst: !fd): $R.result([c:nat] int c, io_error)

(* ============================================================
   Directory operations
   ============================================================ *)

#pub fn dir_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(dir, io_error)

#pub fn dir_close(d: dir): $R.result(int, io_error)

(* Every entry of the directory at path (including . and ..), sorted by
   name; err when the directory cannot be opened or read, or when memory
   for its entries cannot be had (OutOfMemory). *)
#pub fn dir_read
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([k:nat] entries(k), io_error)

#pub fn entries_count {n:int} (es: !entries(n)): int n

(* The most bytes an entry's name has (d_name's size on macOS, the
   largest of the hosts; checked against the host's d_name when this
   package compiles). *)
#pub stadef ENTRY_NAME_MAX = 1024

(* Length of entry i's name, copied whole to name_buf[0, k); the buffer
   holds any name. *)
#pub fn entries_name
  {n:int}{i:nat | i < n}{l:agz}{m:int | m >= ENTRY_NAME_MAX}
  (es: !entries(n), i: int i, name_buf: !$A.arr(byte, l, m), max_len: int m): [k:nat | k < ENTRY_NAME_MAX] int k

#pub fn entries_free {n:int} (es: entries(n)): void

(* ============================================================
   Extra POSIX operations
   ============================================================ *)

#pub fn file_chdir
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, io_error)

(* The modification time of the file at path, in seconds since 1970
   (before it, negative) *)
#pub fn file_mtime
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, io_error)

#pub fn file_exists
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): bool

#pub fn file_mkdir
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int): $R.result(int, io_error)

(* The permission bits (0 to 07777) of the file at path, or why they
   cannot be read. *)
#pub fn file_mode
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result([m:nat | m <= 4095] int m, io_error)

(* Sets the permission bits of the file at path to mode, or says why it
   cannot. *)
#pub fn file_chmod
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n, mode: int): $R.result(int, io_error)

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

#pub fn buf_reader_close(r: buf_reader): $R.result(int, io_error)

(* ============================================================
   Buffered writer
   ============================================================ *)

(* pos < BUF_SIZE bytes are pending: a write that fills the buffer
   writes it out. *)
#pub datavtype buf_writer =
  | {lb:agz}{p:nat | p < BUF_SIZE}
    buf_writer_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int p)

#pub fn buf_writer_create(f: fd): buf_writer

#pub fn buf_write
  {lb:agz}{n:pos}
  (w: !buf_writer, data: !$A.borrow(byte, lb, n), len: int n): $R.result(int, io_error)

#pub fn buf_write_byte(w: !buf_writer, b: int): $R.result(int, io_error)

#pub fn buf_flush(w: !buf_writer): $R.result(int, io_error)

#pub fn buf_writer_close(w: buf_writer): $R.result(int, io_error)

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

(* The C runtime's code for an access and an opening: the one place
   they are encoded *)
fn _access_code (access: access): int =
  case+ access of
  | ReadOnly() => 0
  | WriteOnly() => 1
  | ReadWrite() => 2

fn _opening_code (opening: opening): int =
  case+ opening of
  | OpenExisting() => 0
  | CreateOrOpen() => 1
  | CreateOrTruncate() => 2
  | CreateOrAppend() => 3
  | TruncateExisting() => 4
  | AppendExisting() => 5

(* The error a C runtime failure (a negative code, _file_error_code's
   negated) names: the one place the codes are decoded *)
fn _io_error (failure: int): io_error = let
  val code = ~failure
in
  if code = 1 then NotFound()
  else if code = 2 then PermissionDenied()
  else if code = 3 then AlreadyExists()
  else if code = 4 then NotADirectory()
  else if code = 5 then IsADirectory()
  else if code = 6 then DirectoryNotEmpty()
  else if code = 7 then ReadOnlyFilesystem()
  else if code = 8 then FilesystemLoop()
  else if code = 9 then InvalidFilename()
  else if code = 10 then InvalidInput()
  else if code = 11 then FileTooLarge()
  else if code = 12 then StorageFull()
  else if code = 13 then TooManyOpenFiles()
  else if code = 14 then OutOfMemory()
  else if code = 15 then ResourceBusy()
  else if code = 16 then BrokenPipe()
  else if code = 17 then WouldBlock()
  else if code = 18 then BadDescriptor()
  else if code = 19 then DeviceError()
  else if code = 20 then Unsupported()
  else if code = 21 then CrossesDevices()
  else Unrecognized()
end

implement io_error_text (e) =
  case+ e of
  | NotFound() => "not found"
  | PermissionDenied() => "permission denied"
  | AlreadyExists() => "already exists"
  | NotADirectory() => "not a directory"
  | IsADirectory() => "is a directory"
  | DirectoryNotEmpty() => "directory not empty"
  | ReadOnlyFilesystem() => "read-only file system"
  | FilesystemLoop() => "too many levels of symbolic links"
  | InvalidFilename() => "file name too long"
  | InvalidInput() => "invalid argument"
  | FileTooLarge() => "file too large"
  | StorageFull() => "no space left"
  | TooManyOpenFiles() => "too many open files"
  | OutOfMemory() => "out of memory"
  | ResourceBusy() => "resource busy"
  | BrokenPipe() => "broken pipe"
  | WouldBlock() => "operation would block"
  | BadDescriptor() => "bad file descriptor"
  | DeviceError() => "input/output error"
  | Unsupported() => "operation not supported"
  | CrossesDevices() => "crosses devices"
  | Unrecognized() => "unrecognized error"

(* ============================================================
   File implementations
   ============================================================ *)

implement file_open {lb}{n} (path, path_len, access, opening, mode) = let
  val cpath = _with_cpath(path, path_len)
  val rawfd = $UNSAFE begin $extfcall(int, "_file_open",
    $UNSAFE.castvwtp1{ptr}(cpath), _access_code(access), _opening_code(opening), mode) end
  val () = $A.free<byte>(cpath)
in
  if rawfd >= 0 then $R.ok(fd_mk(rawfd))
  else $R.err(_io_error(rawfd))
end

implement file_read {l}{n}{o} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall([k:int | k <= n] int k, "_file_read", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), len) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(_io_error(r))
end

implement file_write {lb}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  (* _file_write returns len or a failure *)
  val r = $UNSAFE begin $extfcall([k:int | k == n || k < 0] int k, "_file_write", rawfd,
    $UNSAFE.castvwtp1{ptr}(buf), len) end
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(_io_error(r))
end

implement file_close(f) = let
  val+ ~fd_mk(rawfd) = f
  val r = $UNSAFE begin $extfcall(int, "_file_close", rawfd) end
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement file_size {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val sz = $UNSAFE begin $extfcall([s:int] int s, "_file_stat_size",
    $UNSAFE.castvwtp1{ptr}(cpath)) end
  val () = $A.free<byte>(cpath)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(_io_error(sz))
end

implement fd_size(f) = let
  val+ @fd_mk(rawfd) = f
  val sz = $UNSAFE begin $extfcall([s:int] int s, "_file_fd_size", rawfd) end
  prval () = fold@(f)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(_io_error(sz))
end

(* 64 KiB at a time, until r bytes remain to copy. A chunk read past the
   size (the file grew) is copied only up to it; a read of 0 bytes is
   the end of src. *)
implement fd_copy(src, dst) = let
  fun loop {l:agz}{r,c:nat} .<r>.
    (src: !fd, dst: !fd, buf: $A.arr(byte, l, 65536), r: int r, c: int c)
    : @($R.result([c:nat] int c, io_error), $A.arr(byte, l, 65536)) =
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
  else $R.err(_io_error($UNSAFE begin $extfcall(int, "_file_last_failed") end))
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
  else $R.err(_io_error($UNSAFE begin $extfcall(int, "_file_last_failed") end))
end

implement entries_count {n} (es) = let
  val+ @entries_mk(_, k) = es
  val r = k
  prval () = fold@(es)
in r end

implement entries_name {n}{i}{l}{m} (es, i, name_buf, max_len) = let
  val+ @entries_mk(p, _) = es
  val r = $UNSAFE begin $extfcall([k:nat | k < ENTRY_NAME_MAX] int k, "_file_entries_name", p, i,
    $UNSAFE.castvwtp1{ptr}(name_buf)) end
  prval () = fold@(es)
in r end

implement entries_free {n} (es) = let
  val+ ~entries_mk(p, _) = es
in $UNSAFE begin $extfcall(void, "_file_entries_free", p) end end

implement dir_close(d) = let
  (* dir_open makes a dir only of a pointer that is not null *)
  val+ ~dir_mk(dp) = d
  val r = $UNSAFE begin $extfcall(int, "_file_closedir", dp) end
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
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
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement file_mtime {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  var mtime: int = 0
  val r = $UNSAFE begin $extfcall(int, "_file_mtime",
    $UNSAFE.castvwtp1{ptr}(cpath), addr@mtime) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(mtime)
  else $R.err(_io_error(r))
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
  else $R.err(_io_error(m))
end

implement file_chmod {lb}{n} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_chmod",
    $UNSAFE.castvwtp1{ptr}(cpath), mode) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
end

implement file_mkdir {lb}{n} (path, path_len, mode) = let
  val cpath = _with_cpath(path, path_len)
  val r = $UNSAFE begin $extfcall(int, "_file_mkdir",
    $UNSAFE.castvwtp1{ptr}(cpath), mode) end
  val () = $A.free<byte>(cpath)
in
  if r >= 0 then $R.ok(0)
  else $R.err(_io_error(r))
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

(* Where a scan of buf[i..lim) for a newline stops: at the first
   newline, or at lim when there is none *)
fun _scan_nl {lb:agz}{i,lim:nat | i <= lim; lim <= BUF_SIZE} .<lim - i>.
  (ibuf: !$A.arr(byte, lb, BUF_SIZE), i: int i, lim: int lim)
  : [r:int | i <= r; r <= lim] int r =
  if i >= lim then lim
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
    if nl < filled then let
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

(* buf[0, c) written to f: the count, or why it was not *)
fn _write_prefix {lb:agz}{c:pos | c <= BUF_SIZE}
  (f: !fd, buf: $A.arr(byte, lb, BUF_SIZE), c: int c)
  : @($A.arr(byte, lb, BUF_SIZE), $R.result(int, io_error)) = let
  val @(fz, bv) = $A.freeze<byte>(buf)
  val+ @fd_mk(rawfd) = f
  val written = $UNSAFE begin $extfcall(int, "_file_write", rawfd,
    $UNSAFE.castvwtp1{ptr}(bv), c) end
  prval () = fold@(f)
  val () = $A.drop<byte>(fz, bv)
in
  @($A.thaw<byte>(fz), (if written >= 0 then $R.ok(written) else $R.err(_io_error(written))): $R.result(int, io_error))
end

fn _buf_do_flush(w: !buf_writer): $R.result(int, io_error) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos <= 0 then let
    prval () = fold@(w)
  in $R.ok(0) end
  else let
    val @(buf2, r) = _write_prefix(f, buf, pos)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
end

implement buf_flush(w) = _buf_do_flush(w)

(* A full buffer is flushed before the byte is stored; the byte is the
   low 8 bits of b, as before, now without a cast. *)
implement buf_write_byte(w, b) = let
  val+ @buf_writer_mk(f, buf, pos) = w
  val () = $A.set<byte>(buf, pos, $A.int2byte($AR.low_byte(b)))
  val np = pos + 1
in
  if np < 4096 then let
    val () = pos := np
    prval () = fold@(w)
  in $R.ok(1) end
  else let
    val @(buf2, r) = _write_prefix(f, buf, np)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
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
  (w: !buf_writer, data: !$A.borrow(byte, lb, n), len: int n): $R.result(int, io_error) = let
  val+ @buf_writer_mk(f, buf, pos) = w
in
  if pos + len < 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val () = pos := pos + len
    prval () = fold@(w)
  in $R.ok(len) end
  else if pos + len = 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val @(buf2, r) = _write_prefix(f, buf, 4096)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
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
  if pos + len < 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val () = pos := pos + len
    prval () = fold@(w)
  in $R.ok(len) end
  else if pos + len = 4096 then let
    val () = _copy_in(buf, data, pos, 0, len)
    val @(buf2, r) = _write_prefix(f, buf, 4096)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in r end
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
  val () = $R.discard<int><io_error>(flush_r)
  val+ ~buf_writer_mk(f, buf, _) = w
  val () = $A.free<byte>(buf)
in file_close(f) end
