#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* file_open and file_read fail with why: NotFound for a missing file,
   IsADirectory for reading a directory *)

fn check (name: string, got: string, want: string): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

(* Why opening p failed, or "opened" *)
fn open_err {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): string =
  case+ $F.file_open(p, np, $F.ReadOnly(), $F.OpenExisting(), 0) of
  | ~$R.ok(fd) => let
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in "opened" end
  | ~$R.err(e) => $F.io_error_text(e)

(* Why reading p after opening it failed, or "read" *)
fn read_err {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): string =
  case+ $F.file_open(p, np, $F.ReadOnly(), $F.OpenExisting(), 0) of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(16)
      val e = (case+ $F.file_read(fd, buf, 16) of | ~$R.ok(_) => "read" | ~$R.err(e) => $F.io_error_text(e)): string
      val () = $A.free<byte>(buf)
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in e end
  | ~$R.err(e) => $F.io_error_text(e)

implement main0 () = let
  var m = @[char][22]('/', 'n', 'o', '-', 's', 'u', 'c', 'h', '/', 'b', 'a', 't', 's', '-', 'e', 'r', 'r', 'n', 'o', '.', 'x', '\000')
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(m, 22))
  var d = @[char][5]('/', 't', 'm', 'p', '\000')
  val @(fd, bd) = $A.freeze<byte>($S.from_char_array(d, 5))
  val r1 = check("open a missing file", open_err(bm, 22), $F.io_error_text($F.NotFound()))
  val r2 = check("read a directory", read_err(bd, 5), $F.io_error_text($F.IsADirectory()))
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
  val () = $A.drop<byte>(fd, bd)
  val () = $A.free<byte>($A.thaw<byte>(fd))
in
  if r1 && r2 then println! ("ok") else println! ("FAIL")
end
