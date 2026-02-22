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
#include <string.h>

static int _file_open(const char *path, int flags, int mode) {
  return open(path, flags, mode);
}
static int _file_read(int fd, void *buf, int len) {
  return (int)read(fd, buf, (unsigned int)len);
}
static int _file_write(int fd, const void *buf, int len) {
  return (int)write(fd, buf, (unsigned int)len);
}
static int _file_close(int fd) {
  return close(fd);
}
static int _file_stat_size(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) return -1;
  return (int)st.st_size;
}
static void *_file_opendir(const char *path) {
  return (void *)opendir(path);
}
static int _file_readdir(void *dirp, char *name_buf, int max_len) {
  struct dirent *e = readdir(dirp);
  if (!e) return -1;
  int len = (int)strlen(e->d_name);
  if (len > max_len) len = max_len;
  memcpy(name_buf, e->d_name, len);
  return len;
}
static int _file_closedir(void *dirp) {
  return closedir(dirp);
}
static int _file_ptr_nonnull(void *p) {
  return p != (void*)0 ? 1 : 0;
}
#endif
%}
end

(* ============================================================
   Open flags
   ============================================================ *)

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

(* ============================================================
   File operations
   ============================================================ *)

#pub fn file_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n,
   flags: int, mode: int): $R.result(fd, int)

#pub fn file_read
  {l:agz}{n:pos}
  (f: !fd, buf: !$A.arr(byte, l, n), len: int n): $R.result(int, int)

#pub fn file_write
  {lb:agz}{n:pos}
  (f: !fd, buf: !$A.borrow(byte, lb, n), len: int n): $R.result(int, int)

#pub fn file_close(f: fd): $R.result(int, int)

#pub fn file_size
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(int, int)

(* ============================================================
   Directory operations
   ============================================================ *)

#pub fn dir_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): $R.result(dir, int)

#pub fn dir_next
  {l:agz}{n:pos}
  (d: !dir, name_buf: !$A.arr(byte, l, n), max_len: int n): $R.option(int)

#pub fn dir_close(d: dir): $R.result(int, int)

(* ============================================================
   Buffered reader
   ============================================================ *)

#pub stadef BUF_SIZE = 4096

#pub datavtype buf_reader =
  | {lb:agz}
    buf_reader_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int, int)

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

#pub datavtype buf_writer =
  | {lb:agz}
    buf_writer_mk of (fd, $A.arr(byte, lb, BUF_SIZE), int)

#pub fn buf_writer_create(f: fd): buf_writer

#pub fun buf_write
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
  val rawfd = $extfcall(int, "_file_open",
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(cpath) end, flags, mode)
  val () = $A.free<byte>(cpath)
in
  if rawfd >= 0 then $R.ok(fd_mk(rawfd))
  else $R.err(rawfd)
end

implement file_read {l}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $extfcall(int, "_file_read", rawfd,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(buf) end, len)
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(r)
end

implement file_write {lb}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $extfcall(int, "_file_write", rawfd,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(buf) end, len)
  prval () = fold@(f)
in
  if r >= 0 then $R.ok(r)
  else $R.err(r)
end

implement file_close(f) = let
  val+ ~fd_mk(rawfd) = f
  val r = $extfcall(int, "_file_close", rawfd)
in
  if $AR.eq_int_int(r, 0) then $R.ok(0)
  else $R.err(r)
end

implement file_size {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val sz = $extfcall(int, "_file_stat_size",
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(cpath) end)
  val () = $A.free<byte>(cpath)
in
  if sz >= 0 then $R.ok(sz)
  else $R.err(~1)
end

(* ============================================================
   Directory implementations
   ============================================================ *)

implement dir_open {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val dp = $extfcall(ptr, "_file_opendir",
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(cpath) end)
  val () = $A.free<byte>(cpath)
  val nonnull = $extfcall(int, "_file_ptr_nonnull", dp)
in
  if nonnull > 0 then $R.ok(dir_mk(dp))
  else $R.err(~1)
end

implement dir_next {l}{n} (d, name_buf, max_len) = let
  val+ @dir_mk(dp) = d
  val r = $extfcall(int, "_file_readdir", dp,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(name_buf) end, max_len)
  prval () = fold@(d)
in
  if r >= 0 then $R.some(r)
  else $R.none()
end

implement dir_close(d) = let
  val+ ~dir_mk(dp) = d
  val nonnull = $extfcall(int, "_file_ptr_nonnull", dp)
  val r = if nonnull > 0 then $extfcall(int, "_file_closedir", dp) else ~1
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

fn _buf_refill(r: !buf_reader): int = let
  val+ @buf_reader_mk(f, buf, filled, pos) = r
  val+ @fd_mk(rawfd) = f
  val n = $extfcall(int, "_file_read", rawfd,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(buf) end, 4096)
  prval () = fold@(f)
  val () = filled := (if n > 0 then n else 0)
  val () = pos := 0
  prval () = fold@(r)
in n end

implement buf_read {l}{n} (r, dst, len) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = r
  val avail = filled - pos
in
  if avail > 0 then let
    val to_copy = (if avail < len then avail else len): int
    val pos1 = g1ofg0(pos)
  in
    if pos1 >= 0 then
      if pos1 < 4096 then let
        fun loop {l:agz}{n:pos}{lb:agz}{k:nat | k <= n} .<n - k>.
          (dst: !$A.arr(byte, l, n), src: !$A.arr(byte, lb, 4096),
           di: int k, si: int, n: int n, count: int): void =
          if di >= n then ()
          else if di >= count then ()
          else let val si1 = g1ofg0(si) in
            if si1 >= 0 then
              if si1 < 4096 then let
                val () = $A.set<byte>(dst, di, $A.get<byte>(src, si1))
              in loop(dst, src, di + 1, si + 1, n, count) end
              else ()
            else ()
          end
        val () = loop(dst, ibuf, 0, pos, len, to_copy)
        val () = pos := pos + to_copy
        prval () = fold@(r)
      in $R.some(to_copy) end
      else let prval () = fold@(r) in $R.some(0) end
    else let prval () = fold@(r) in $R.some(0) end
  end
  else let
    prval () = fold@(r)
    val n = _buf_refill(r)
  in
    if n > 0 then buf_read(r, dst, len)
    else $R.none()
  end
end

implement buf_read_line {l}{n} (r, buf, max_len) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = r
in
  if pos >= filled then let
    prval () = fold@(r)
    val n = _buf_refill(r)
  in
    if n > 0 then buf_read_line(r, buf, max_len)
    else $R.none()
  end
  else let
    val pos1 = g1ofg0(pos)
  in
    if pos1 >= 0 then
      if pos1 < 4096 then let
        fun scan {lb:agz}{k:nat | k <= 4096} .<4096 - k>.
          (ibuf: !$A.arr(byte, lb, 4096), from: int k, limit: int): int =
          if from >= limit then ~1
          else if from >= 4096 then ~1
          else if byte2int0($A.get<byte>(ibuf, from)) = 10 then from
          else scan(ibuf, from + 1, limit)
        val nl_pos = scan(ibuf, pos1, (if filled < 4096 then filled else 4096))
      in
        if nl_pos >= 0 then let
          val line_len = nl_pos - pos
          val copy_len = (if line_len > max_len then max_len else line_len): int
          fun cloop {l:agz}{n:pos}{lb:agz}{k:nat | k <= n} .<n - k>.
            (dst: !$A.arr(byte, l, n), src: !$A.arr(byte, lb, 4096),
             di: int k, si: int, n: int n, count: int): void =
            if di >= n then ()
            else if di >= count then ()
            else let val si1 = g1ofg0(si) in
              if si1 >= 0 then
                if si1 < 4096 then let
                  val () = $A.set<byte>(dst, di, $A.get<byte>(src, si1))
                in cloop(dst, src, di + 1, si + 1, n, count) end
                else ()
              else ()
            end
          val () = cloop(buf, ibuf, 0, pos, max_len, copy_len)
          val () = pos := nl_pos + 1
          prval () = fold@(r)
        in $R.some(copy_len) end
        else let
          val rest_len = filled - pos
          val copy_len = (if rest_len > max_len then max_len else rest_len): int
          fun cloop2 {l:agz}{n:pos}{lb:agz}{k:nat | k <= n} .<n - k>.
            (dst: !$A.arr(byte, l, n), src: !$A.arr(byte, lb, 4096),
             di: int k, si: int, n: int n, count: int): void =
            if di >= n then ()
            else if di >= count then ()
            else let val si1 = g1ofg0(si) in
              if si1 >= 0 then
                if si1 < 4096 then let
                  val () = $A.set<byte>(dst, di, $A.get<byte>(src, si1))
                in cloop2(dst, src, di + 1, si + 1, n, count) end
                else ()
              else ()
            end
          val () = cloop2(buf, ibuf, 0, pos, max_len, copy_len)
          val () = pos := filled
          prval () = fold@(r)
        in $R.some(copy_len) end
      end
      else let prval () = fold@(r) in $R.none() end
    else let prval () = fold@(r) in $R.none() end
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
    val written = $extfcall(int, "_file_write", rawfd,
      $UNSAFE begin $UNSAFE.castvwtp1{ptr}(bv) end, pos)
    prval () = fold@(f)
    val () = $A.drop<byte>(fz, bv)
    val buf2 = $A.thaw<byte>(fz)
    val () = buf := buf2
    val () = pos := 0
    prval () = fold@(w)
  in
    if written >= 0 then $R.ok(written)
    else $R.err(written)
  end
end

implement buf_flush(w) = _buf_do_flush(w)

implement buf_write_byte(w, b) = let
  val+ @buf_writer_mk(f, buf, pos) = w
  val pos1 = g1ofg0(pos)
in
  if pos1 >= 0 then
    if pos1 < 4096 then let
      val () = $A.set<byte>(buf, pos1, $A.int2byte($AR.checked_byte(b)))
      val () = pos := pos + 1
      prval () = fold@(w)
    in
      if pos1 + 1 >= 4096 then _buf_do_flush(w)
      else $R.ok(1)
    end
    else let
      prval () = fold@(w)
      val r = _buf_do_flush(w)
    in
      case+ r of
      | ~$R.ok(_) => buf_write_byte(w, b)
      | ~$R.err(e) => $R.err(e)
    end
  else let prval () = fold@(w) in $R.err(~1) end
end

implement buf_write {lb}{n} (w, data, len) = let
  val+ @buf_writer_mk(f, buf, pos) = w
  val avail = 4096 - pos
in
  if len <= avail then let
    val pos1 = g1ofg0(pos)
  in
    if pos1 >= 0 then
      if pos1 < 4096 then let
        fun cloop
          {ld:agz}{ls:agz}{n:pos}{k:nat | k <= n} .<n - k>.
          (dst: !$A.arr(byte, ld, 4096), src: !$A.borrow(byte, ls, n),
           di: int, si: int k, n: int n): void =
          if si >= n then ()
          else let val di1 = g1ofg0(di) in
            if di1 >= 0 then
              if di1 < 4096 then let
                val () = $A.set<byte>(dst, di1, $A.read<byte>(src, si))
              in cloop(dst, src, di + 1, si + 1, n) end
              else ()
            else ()
          end
        val () = cloop(buf, data, pos, 0, len)
        val new_pos = pos + len
        val () = pos := new_pos
        prval () = fold@(w)
      in
        if new_pos >= 4096 then _buf_do_flush(w)
        else $R.ok(len)
      end
      else let prval () = fold@(w) in $R.err(~1) end
    else let prval () = fold@(w) in $R.err(~1) end
  end
  else let
    prval () = fold@(w)
    val r = _buf_do_flush(w)
  in
    case+ r of
    | ~$R.ok(_) => buf_write(w, data, len)
    | ~$R.err(e) => $R.err(e)
  end
end

implement buf_writer_close(w) = let
  val flush_r = _buf_do_flush(w)
  val () = $R.discard<int><int>(flush_r)
  val+ ~buf_writer_mk(f, buf, _) = w
  val () = $A.free<byte>(buf)
in file_close(f) end
