#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* file_chmod sets the permission bits that file_mode reads back (the
   harness runs this in a scratch directory it owns), and both fail
   with ENOENT (2) for a missing file. *)

fn check (name: string, got: string, want: string): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

(* Whether file_mode gave p the mode want *)
fn mode_is {lp:agz}{np:pos | np < 1048576}
  (name: string, p: !$A.borrow(byte, lp, np), np: int np, want: int): bool =
  case+ $F.file_mode(p, np) of
  | ~$R.ok(m) => let
      val ok = (m = want)
      val () = (if ok then () else println! ("FAIL ", name, ": got ", m, ", want ", want))
    in ok end
  | ~$R.err(e) => let
      val () = println! ("FAIL ", name, ": ", $F.io_error_text(e))
    in false end

(* Why file_mode failed for p, or "read" *)
fn mode_err {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): string =
  case+ $F.file_mode(p, np) of
  | ~$R.ok(_) => "read"
  | ~$R.err(e) => $F.io_error_text(e)

(* What chmod p to m gave: "changed", or why not *)
fn chmod_to {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np, m: int): string =
  case+ $F.file_chmod(p, np, m) of
  | ~$R.ok(_) => "changed"
  | ~$R.err(e) => $F.io_error_text(e)

implement main0 () = let
  var f = @[char][7]('m', 'o', 'd', 'e', '.', 'x', '\000')
  val @(ff, bf) = $A.freeze<byte>($S.from_char_array(f, 7))
  var m = @[char][22]('/', 'n', 'o', '-', 's', 'u', 'c', 'h', '/', 'b', 'a', 't', 's', '-', 'm', 'o', 'd', 'e', '.', 'x', '\000', '\000')
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(m, 22))
  (* create mode.x *)
  val () = (case+ $F.file_open(bf, 7, $F.WriteOnly(), $F.CreateOrOpen(), 420) of
    | ~$R.ok(fd) => $R.discard<int><$F.io_error>($F.file_close(fd))
    | ~$R.err(_) => ())
  val r1 = check("chmod 0751", chmod_to(bf, 7, 489), "changed")
  val r2 = mode_is("mode after chmod 0751", bf, 7, 489)
  val r3 = check("chmod 0600", chmod_to(bf, 7, 384), "changed")
  val r4 = mode_is("mode after chmod 0600", bf, 7, 384)
  val r5 = check("mode of a missing file", mode_err(bm, 22), $F.io_error_text($F.NotFound()))
  val r6 = check("chmod a missing file", chmod_to(bm, 22, 384), $F.io_error_text($F.NotFound()))
  val () = $A.drop<byte>(ff, bf)
  val () = $A.free<byte>($A.thaw<byte>(ff))
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
in
  if r1 && r2 && r3 && r4 && r5 && r6 then println! ("ok") else println! ("FAIL")
end
