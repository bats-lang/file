#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* file_open and file_read fail with the errno, as Rust's io::Error
   carries it: ENOENT (2) for a missing file, EISDIR (21 on Linux,
   macOS and the BSDs) for reading a directory. *)

fn check (name: string, got: int, want: int): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

(* The errno of opening p, or 0 when it opened *)
fn open_err {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.file_open(p, np, 0, 0) of
  | ~$R.ok(fd) => let
      val () = $R.discard<int><int>($F.file_close(fd))
    in 0 end
  | ~$R.err(e) => e

(* The errno of reading p after opening it, or 0 when the read worked *)
fn read_err {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.file_open(p, np, 0, 0) of
  | ~$R.ok(fd) => let
      val buf = $A.alloc<byte>(16)
      val e = (case+ $F.file_read(fd, buf, 16) of | ~$R.ok(_) => 0 | ~$R.err(e) => e): int
      val () = $A.free<byte>(buf)
      val () = $R.discard<int><int>($F.file_close(fd))
    in e end
  | ~$R.err(e) => ~e

implement main0 () = let
  var m = @[char][22]('/', 'n', 'o', '-', 's', 'u', 'c', 'h', '/', 'b', 'a', 't', 's', '-', 'e', 'r', 'r', 'n', 'o', '.', 'x', '\000')
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(m, 22))
  var d = @[char][5]('/', 't', 'm', 'p', '\000')
  val @(fd, bd) = $A.freeze<byte>($S.from_char_array(d, 5))
  val r1 = check("open a missing file", open_err(bm, 22), 2)
  val r2 = check("read a directory", read_err(bd, 5), 21)
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
  val () = $A.drop<byte>(fd, bd)
  val () = $A.free<byte>($A.thaw<byte>(fd))
in
  if r1 && r2 then println! ("ok") else println! ("FAIL")
end
