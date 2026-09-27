#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* Opens and closes a directory handle, fails to open a missing one,
   and stats both paths. It runs under valgrind: the handle (a DIR the
   C library allocates) and the C path buffers must all be freed.
   Exits 1 on a wrong outcome. *)

(* 0: opened and closed; 1: open failed; 2: close failed *)
fn open_close {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.dir_open(p, np) of
  | ~$R.ok(d) => (case+ $F.dir_close(d) of ~$R.ok(_) => 0 | ~$R.err(_) => 2)
  | ~$R.err(_) => 1

(* 0: has an mtime; 1: none *)
fn mtime {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.file_mtime(p, np) of
  | ~$R.ok(_) => 0
  | ~$R.err(_) => 1

implement main0 () = let
  var d = @[char][4]('/', 't', 'm', 'p')
  val @(fd, bd) = $A.freeze<byte>($S.from_char_array(d, 4))
  var m = @[char][19]('/', 'n', 'o', '-', 's', 'u', 'c', 'h', '/', 'b', 'a', 't', 's', '-', 'd', 'i', 'r', 's', 'x')
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(m, 19))
  val r1 = open_close(bd, 4)
  val r2 = open_close(bm, 19)
  val e1 = $F.file_exists(bd, 4)
  val e2 = $F.file_exists(bm, 19)
  val t1 = mtime(bd, 4)
  val t2 = mtime(bm, 19)
  val () = $A.drop<byte>(fd, bd)
  val () = $A.free<byte>($A.thaw<byte>(fd))
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
  val ok = r1 = 0 && r2 = 1 && e1 && ~e2 && t1 = 0 && t2 = 1
  val () = (if ok then () else println! ("FAIL: ", r1, " ", r2, " ", t1, " ", t2))
in if ok then () else exit(1) end
