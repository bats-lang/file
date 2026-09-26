#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* file_chmod sets the permission bits that file_mode reads back (the
   harness runs this in a scratch directory it owns), and both fail
   with ENOENT (2) for a missing file. *)

fn check (name: string, got: int, want: int): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

(* The mode of p, or ~errno *)
fn mode_of {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.file_mode(p, np) of | ~$R.ok(m) => m | ~$R.err(e) => ~e

(* 0 after chmod p to m, or ~errno *)
fn chmod_to {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np, m: int): int =
  case+ $F.file_chmod(p, np, m) of | ~$R.ok(_) => 0 | ~$R.err(e) => ~e

implement main0 () = let
  var f = @[char][7]('m', 'o', 'd', 'e', '.', 'x', '\000')
  val @(ff, bf) = $A.freeze<byte>($S.from_char_array(f, 7))
  var m = @[char][22]('/', 'n', 'o', '-', 's', 'u', 'c', 'h', '/', 'b', 'a', 't', 's', '-', 'm', 'o', 'd', 'e', '.', 'x', '\000', '\000')
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(m, 22))
  (* create mode.x *)
  val () = (case+ $F.file_open(bf, 7, 65, 420) (* O_WRONLY + O_CREAT *) of
    | ~$R.ok(fd) => $R.discard<int><int>($F.file_close(fd))
    | ~$R.err(_) => ())
  val r1 = check("chmod 0751", chmod_to(bf, 7, 489), 0)
  val r2 = check("mode after chmod 0751", mode_of(bf, 7), 489)
  val r3 = check("chmod 0600", chmod_to(bf, 7, 384), 0)
  val r4 = check("mode after chmod 0600", mode_of(bf, 7), 384)
  val r5 = check("mode of a missing file", mode_of(bm, 22), ~2)
  val r6 = check("chmod a missing file", chmod_to(bm, 22, 384), ~2)
  val () = $A.drop<byte>(ff, bf)
  val () = $A.free<byte>($A.thaw<byte>(ff))
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
in
  if r1 && r2 && r3 && r4 && r5 && r6 then println! ("ok") else println! ("FAIL")
end
