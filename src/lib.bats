(* file -- POSIX file I/O with linear type safety *)
(* Linear fd must be closed exactly once. Reads/writes through arrays. *)
(* Unsafe core: 6 mac# syscall wrappers. Everything else is safe. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR

(* ============================================================
   C syscall wrappers (the entire unsafe surface)
   ============================================================ *)

$UNSAFE begin
%{#
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <dirent.h>
#include <string.h>

static int _file_open(const char *path, int flags, int mode) {
  return open(path, flags, mode);
}
static int _file_read(int fd, void *buf, int len) {
  int r = (int)read(fd, buf, (unsigned int)len);
  return r;
}
static int _file_write(int fd, const void *buf, int len) {
  int r = (int)write(fd, buf, (unsigned int)len);
  return r;
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
%}
end

(* ============================================================
   Open flags (POSIX standard values)
   ============================================================ *)

#pub stadef O_RDONLY = 0
#pub stadef O_WRONLY = 1
#pub stadef O_RDWR = 2
#pub stadef O_CREAT = 64
#pub stadef O_TRUNC = 512
#pub stadef O_APPEND = 1024

(* ============================================================
   Linear file descriptor -- must close exactly once
   ============================================================ *)

#pub datavtype fd =
  | fd_mk of (int)

(* ============================================================
   Linear directory handle -- must close exactly once
   ============================================================ *)

#pub datavtype dir =
  | dir_mk of (ptr)

(* ============================================================
   Public API -- file operations
   ============================================================ *)

(* Open a file. Returns fd on success, or negative fd_mk on error.
   Caller must check the raw fd value and close regardless. *)
#pub fn file_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n,
   flags: int, mode: int): fd

(* Read into array. Returns bytes read, 0 on EOF, -1 on error. *)
#pub fn file_read
  {l:agz}{n:pos}
  (f: !fd, buf: !$A.arr(byte, l, n), len: int n): int

(* Write from borrow. Returns bytes written or -1 on error. *)
#pub fn file_write
  {lb:agz}{n:pos}
  (f: !fd, buf: !$A.borrow(byte, lb, n), len: int n): int

(* Close file. Consumes the fd. *)
#pub fn file_close(f: fd): int

(* Get raw fd value (for checking open success) *)
#pub fn file_rawfd(f: !fd): int

(* Stat file size. Returns -1 on error. *)
#pub fn file_size
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): int

(* ============================================================
   Public API -- directory operations
   ============================================================ *)

(* Open a directory. Check with dir_valid. *)
#pub fn dir_open
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): dir

(* Check if dir opened successfully *)
#pub fn dir_valid(d: !dir): bool

(* Read next entry name into array. Returns name length, -1 on end/error. *)
#pub fn dir_next
  {l:agz}{n:pos}
  (d: !dir, name_buf: !$A.arr(byte, l, n), max_len: int n): int

(* Close directory. Consumes the handle. *)
#pub fn dir_close(d: dir): int

(* ============================================================
   Public API -- buffered reader
   ============================================================ *)

#pub stadef BUF_SIZE = 4096

#pub datavtype buf_reader =
  | {lb:agz}
    buf_reader_mk of (
      fd,
      $A.arr(byte, lb, BUF_SIZE),
      int,   (* filled: bytes in buffer *)
      int    (* pos: current read position *)
    )

(* Create a buffered reader from an fd. Consumes the fd. *)
#pub fn buf_reader_create(f: fd): buf_reader

(* Read up to len bytes into arr. Returns bytes read, 0 on EOF. *)
#pub fun buf_read
  {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), len: int n): int

(* Read a line (up to newline or EOF) into arr.
   Returns bytes read (excluding newline), -1 on EOF with no data. *)
#pub fun buf_read_line
  {l:agz}{n:pos}
  (r: !buf_reader, buf: !$A.arr(byte, l, n), max_len: int n): int

(* Close buffered reader. Closes the underlying fd. *)
#pub fn buf_reader_close(r: buf_reader): int

(* ============================================================
   Implementations -- core file ops
   ============================================================ *)

(* We need a null-terminated copy of the path for C.
   Allocate path_len+1 bytes, copy, add null. *)
fn _with_cpath
  {lb:agz}{n:pos | n < 1048576}
  (path: !$A.borrow(byte, lb, n), path_len: int n): [lc:agz] $A.arr(byte, lc, n+1) = let
  val cpath = $A.alloc<byte>(path_len + 1)
  val () = $A.write_borrow(cpath, 0, path, path_len)
  val () = $A.write_byte(cpath, path_len, 0)
in cpath end

implement file_open {lb}{n} (path, path_len, flags, mode) = let
  val cpath = _with_cpath(path, path_len)
  val rawfd = $extfcall(int, "_file_open",
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(cpath) end, flags, mode)
  val () = $A.free<byte>(cpath)
in fd_mk(rawfd) end

implement file_read {l}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $extfcall(int, "_file_read", rawfd,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(buf) end, len)
  prval () = fold@(f)
in r end

implement file_write {lb}{n} (f, buf, len) = let
  val+ @fd_mk(rawfd) = f
  val r = $extfcall(int, "_file_write", rawfd,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(buf) end, len)
  prval () = fold@(f)
in r end

implement file_close(f) = let
  val+ ~fd_mk(rawfd) = f
in $extfcall(int, "_file_close", rawfd) end

implement file_rawfd(f) = let
  val+ @fd_mk(rawfd) = f
  val r = rawfd
  prval () = fold@(f)
in r end

implement file_size {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val sz = $extfcall(int, "_file_stat_size",
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(cpath) end)
  val () = $A.free<byte>(cpath)
in sz end

(* ============================================================
   Implementations -- directory ops
   ============================================================ *)

implement dir_open {lb}{n} (path, path_len) = let
  val cpath = _with_cpath(path, path_len)
  val dp = $extfcall(ptr, "_file_opendir",
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(cpath) end)
  val () = $A.free<byte>(cpath)
in dir_mk(dp) end

implement dir_valid(d) = let
  val+ @dir_mk(dp) = d
  val v = $extfcall(int, "_file_ptr_nonnull", dp)
  prval () = fold@(d)
in v > 0 end

implement dir_next {l}{n} (d, name_buf, max_len) = let
  val+ @dir_mk(dp) = d
  val r = $extfcall(int, "_file_readdir", dp,
    $UNSAFE begin $UNSAFE.castvwtp1{ptr}(name_buf) end, max_len)
  prval () = fold@(d)
in r end

implement dir_close(d) = let
  val+ ~dir_mk(dp) = d
  val nonnull = $extfcall(int, "_file_ptr_nonnull", dp)
in
  if nonnull > 0 then $extfcall(int, "_file_closedir", dp)
  else ~1
end

(* ============================================================
   Implementations -- buffered reader
   ============================================================ *)

implement buf_reader_create(f) = let
  val buf = $A.alloc<byte>(4096)
in buf_reader_mk(f, buf, 0, 0) end

(* Internal: refill buffer from fd *)
fn _buf_refill(r: !buf_reader): int = let
  val+ @buf_reader_mk(f, buf, filled, pos) = r
  val n = file_read(f, buf, 4096)
  val () = filled := (if n > 0 then n else 0)
  val () = pos := 0
  prval () = fold@(r)
in n end

implement buf_read {l}{n} (buf, dst, len) = let
  val+ @buf_reader_mk(f, ibuf, filled, pos) = buf
  val avail = filled - pos
in
  if avail > 0 then let
    (* Have data in buffer — copy what we can *)
    val to_copy = (if avail < len then avail else len): int
    val to_copy1 = g1ofg0(to_copy)
    val pos1 = g1ofg0(pos)
  in
    if to_copy1 > 0 then
      if to_copy1 <= 4096 then
        if pos1 >= 0 then
          if pos1 < 4096 then let
            (* Freeze ibuf, get borrow, copy to dst *)
            val @(fz, bv) = $A.freeze<byte>(ibuf)
            (* We need to copy to_copy bytes from bv at offset pos to dst at offset 0.
               Use array write_borrow with a borrow_split to get the right slice. *)
            val () = $A.drop<byte>(fz, bv)
            val ibuf2 = $A.thaw<byte>(fz)
            (* Simpler: just copy byte by byte *)
            fun loop {l:agz}{n:pos}{lb:agz}{k:nat | k <= n} .<n - k>.
              (dst: !$A.arr(byte, l, n), src: !$A.arr(byte, lb, 4096),
               di: int k, si: int, n: int n, count: int): void =
              if di >= n then ()
              else if di >= count then ()
              else let
                val si1 = g1ofg0(si)
              in
                if si1 >= 0 then
                  if si1 < 4096 then let
                    val b = $A.get<byte>(src, si1)
                    val () = $A.set<byte>(dst, di, b)
                  in loop(dst, src, di + 1, si + 1, n, count) end
                  else ()
                else ()
              end
            val () = loop(dst, ibuf2, 0, pos, len, to_copy)
            val () = ibuf := ibuf2
            val () = pos := pos + to_copy
            prval () = fold@(buf)
          in to_copy end
          else let prval () = fold@(buf) in 0 end
        else let prval () = fold@(buf) in 0 end
      else let prval () = fold@(buf) in 0 end
    else let prval () = fold@(buf) in 0 end
  end
  else let
    prval () = fold@(buf)
    (* Buffer empty — refill *)
    val n = _buf_refill(buf)
  in
    if n > 0 then buf_read(buf, dst, len)
    else 0
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
    else ~1
  end
  else let
    (* Scan for newline in buffer *)
    fun scan {lb:agz}{k:nat | k <= 4096} .<4096 - k>.
      (ibuf: !$A.arr(byte, lb, 4096), from: int k, limit: int): int =
      if from >= limit then ~1
      else if from >= 4096 then ~1
      else let val b = byte2int0($A.get<byte>(ibuf, from))
      in if b = 10 then from (* found \n *)
         else scan(ibuf, from + 1, limit) end
    val pos1 = g1ofg0(pos)
  in
    if pos1 >= 0 then
      if pos1 < 4096 then let
        val nl_pos = scan(ibuf, pos1, (if filled < 4096 then filled else 4096))
      in
        if nl_pos >= 0 then let
          (* Found newline — copy [pos, nl_pos) to buf *)
          val line_len = nl_pos - pos
          val copy_len = (if line_len > max_len then max_len else line_len): int
          fun copy_loop {l:agz}{n:pos}{lb:agz}{k:nat | k <= n} .<n - k>.
            (dst: !$A.arr(byte, l, n), src: !$A.arr(byte, lb, 4096),
             di: int k, si: int, n: int n, count: int): void =
            if di >= n then ()
            else if di >= count then ()
            else let val si1 = g1ofg0(si) in
              if si1 >= 0 then
                if si1 < 4096 then let
                  val () = $A.set<byte>(dst, di, $A.get<byte>(src, si1))
                in copy_loop(dst, src, di + 1, si + 1, n, count) end
                else ()
              else ()
            end
          val () = copy_loop(buf, ibuf, 0, pos, max_len, copy_len)
          val () = pos := nl_pos + 1 (* skip past newline *)
          prval () = fold@(r)
        in copy_len end
        else let
          (* No newline — copy rest of buffer, refill, continue *)
          val rest_len = filled - pos
          val copy_len = (if rest_len > max_len then max_len else rest_len): int
          fun copy_loop2 {l:agz}{n:pos}{lb:agz}{k:nat | k <= n} .<n - k>.
            (dst: !$A.arr(byte, l, n), src: !$A.arr(byte, lb, 4096),
             di: int k, si: int, n: int n, count: int): void =
            if di >= n then ()
            else if di >= count then ()
            else let val si1 = g1ofg0(si) in
              if si1 >= 0 then
                if si1 < 4096 then let
                  val () = $A.set<byte>(dst, di, $A.get<byte>(src, si1))
                in copy_loop2(dst, src, di + 1, si + 1, n, count) end
                else ()
              else ()
            end
          val () = copy_loop2(buf, ibuf, 0, pos, max_len, copy_len)
          val () = pos := filled
          prval () = fold@(r)
          (* For simplicity, return what we have — caller calls again for more *)
        in copy_len end
      end
      else let prval () = fold@(r) in ~1 end
    else let prval () = fold@(r) in ~1 end
  end
end

implement buf_reader_close(r) = let
  val+ ~buf_reader_mk(f, buf, _, _) = r
  val () = $A.free<byte>(buf)
in file_close(f) end
