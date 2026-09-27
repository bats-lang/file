#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* fd_copy copies a 200003-byte file (three 64 KiB chunks and a partial
   one) byte for byte, and an empty file as 0 bytes; fd_size reports
   the copy's size. *)

#define N 200003

fun fill {l:agz}{i:nat | i <= 200003} .<200003 - i>. (a: !$A.arr(byte, l, 200003), i: int i): void =
  if i >= N then ()
  else let val () = $A.set<byte>(a, i, $A.int2byte(nmod(i, 251))) in fill(a, i + 1) end

(* Whether a[0, N) holds the fill pattern *)
fun same {l:agz}{i:nat | i <= 200003} .<200003 - i>. (a: !$A.arr(byte, l, 200004), i: int i): bool =
  if i >= N then true
  else if byte2int0($A.get<byte>(a, i)) = nmod(i, 251) then same(a, i + 1)
  else false

(* Prints fd's size, and how many bytes a read of it gives and whether
   they hold the fill pattern *)
fn show (fd: !$F.fd): void = let
  val () = (case+ $F.fd_size(fd) of
    | ~$R.ok(s) => println! ("size ", s)
    | ~$R.err(e) => println! ("FAIL: size ", e))
  val buf = $A.alloc<byte>(N + 1)
  val k = (case+ $F.file_read(fd, buf, N + 1) of
    | ~$R.ok(k) => k
    | ~$R.err(e) => ~e): int
  val ok = same(buf, 0)
  val () = println! ("read ", k, ", same ", ok)
in $A.free<byte>(buf) end

(* Opens the 5-byte path in chars with flags and mode *)
fn open5 (chars: &(@[char][5]), flags: int, mode: int): $R.result($F.fd, int) = let
  val @(fz, bv) = $A.freeze<byte>($S.from_char_array(chars, 5))
  val r = $F.file_open(bv, 5, flags, mode)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* Copies src to dst (both 5-byte paths); the count, or ~errno *)
fn copy5 (src: &(@[char][5]), dst: &(@[char][5])): int =
  case+ open5(src, 0, 0) of
  | ~$R.err(e) => ~e
  | ~$R.ok(sf) =>
    (case+ open5(dst, 1 + 64 + 512, 420) of
     | ~$R.err(e) => let val () = $R.discard<int><int>($F.file_close(sf)) in ~e end
     | ~$R.ok(df) => let
         val c = (case+ $F.fd_copy(sf, df) of | ~$R.ok(c) => c | ~$R.err(e) => ~e): int
         val () = $R.discard<int><int>($F.file_close(sf))
         val () = $R.discard<int><int>($F.file_close(df))
       in c end)

implement main0 () = let
  var src = @[char][5]('c', '.', 's', 'r', 'c')
  var dst = @[char][5]('c', '.', 'd', 's', 't')
  var emp = @[char][5]('e', '.', 's', 'r', 'c')
  var edst = @[char][5]('e', '.', 'd', 's', 't')
  val a = $A.alloc<byte>(N)
  val () = fill(a, 0)
  val @(fa, ba) = $A.freeze<byte>(a)
  val () = (case+ open5(src, 1 + 64 + 512, 420) of
    | ~$R.ok(fd) => let
        val () = (case+ $F.file_write(fd, ba, N) of
          | ~$R.ok(k) => println! ("wrote ", k)
          | ~$R.err(e) => println! ("FAIL: write ", e))
      in $R.discard<int><int>($F.file_close(fd)) end
    | ~$R.err(e) => println! ("FAIL: create ", e))
  val () = $A.drop<byte>(fa, ba)
  val () = $A.free<byte>($A.thaw<byte>(fa))
  val () = println! ("copied ", copy5(src, dst))
  val () = (case+ open5(dst, 0, 0) of
    | ~$R.ok(fd) => let
        val () = show(fd)
      in $R.discard<int><int>($F.file_close(fd)) end
    | ~$R.err(e) => println! ("FAIL: open copy ", e))
  val () = (case+ open5(emp, 1 + 64 + 512, 420) of
    | ~$R.ok(fd) => $R.discard<int><int>($F.file_close(fd))
    | ~$R.err(e) => println! ("FAIL: create empty ", e))
in println! ("copied empty ", copy5(emp, edst)) end
