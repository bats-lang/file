#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
#use file as F
#use result as R
#use str as S

(* One byte, then a 5000-byte block (larger than the 4096-byte buffer)
   through buf_write; the file must hold exactly those 5001 bytes. The
   previous implementation never returned from the second write. *)
fun fill {l:agz}{i:nat | i <= 5000} .<5000 - i>. (a: !$A.arr(byte, l, 5000), i: int i): void =
  if i >= 5000 then ()
  else let val () = $A.set<byte>(a, i, $A.int2byte($AR.low_byte(i))) in fill(a, i + 1) end

(* Sum of the bytes read until EOF, and their count. *)
fun drain {l:agz}{k:nat} .<k>. (r: !$F.buf_reader, buf: !$A.arr(byte, l, 4096), f: int k, sum: int, cnt: int): @(int, int) =
  if f <= 0 then @(sum, cnt)
  else (case+ $F.buf_read(r, buf, 4096) of
    | ~$R.some(n) => let
        fun add {i:nat | i <= 4096} .<4096 - i>. (buf: !$A.arr(byte, l, 4096), i: int i, n: int, s: int): int =
          if i >= 4096 then s else if i >= n then s
          else add(buf, i + 1, n, s + byte2int0($A.get<byte>(buf, i)))
      in drain(r, buf, f - 1, add(buf, 0, n, sum), cnt + n) end
    | ~$R.none() => @(sum, cnt))

implement main0 () = let
  var p = @[char][23]('/', 't', 'm', 'p', '/', 'b', 'a', 't', 's', '_', 'b', 'i', 'g', 'w', 'r', 'i', 't', 'e', '.', 'b', 'i', 'n', '\000')
  val @(fp, bp) = $A.freeze<byte>($S.from_char_array(p, 23))
  val big = $A.alloc<byte>(5000)
  val () = fill(big, 0)
  val @(fb, bb) = $A.freeze<byte>(big)
  val wrote = (case+ $F.file_open(bp, 23, $F.WriteOnly(), $F.CreateOrTruncate(), 420) of
    | ~$R.ok(fd) => let
        val w = $F.buf_writer_create(fd)
        val () = $R.discard<int><$F.io_error>($F.buf_write_byte(w, 7))
        val ok = (case+ $F.buf_write(w, bb, 5000) of | ~$R.ok(_) => true | ~$R.err(_) => false): bool
        val () = $R.discard<int><$F.io_error>($F.buf_writer_close(w))
      in ok end
    | ~$R.err(_) => false): bool
  val () = $A.drop<byte>(fb, bb)
  val () = $A.free<byte>($A.thaw<byte>(fb))
  (* expected sum: 7 + sum of (i mod 256) for i < 5000 *)
  fun expect {i:nat | i <= 5000} .<5000 - i>. (i: int i, s: int): int =
    if i >= 5000 then s else expect(i + 1, s + $AR.low_byte(i))
  val want = expect(0, 7)
  val @(sum, cnt) = (case+ $F.file_open(bp, 23, $F.ReadOnly(), $F.OpenExisting(), 0) of
    | ~$R.ok(fd) => let
        val r = $F.buf_reader_create(fd)
        val buf = $A.alloc<byte>(4096)
        val res = drain(r, buf, 10, 0, 0)
        val () = $A.free<byte>(buf)
        val () = $R.discard<int><$F.io_error>($F.buf_reader_close(r))
      in res end
    | ~$R.err(_) => @(~1, ~1)): @(int, int)
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
  val ok = wrote && cnt = 5001 && sum = want
in
  if ok then println! ("bigwrite: all cases pass")
  else let
    val () = println! ("FAIL bigwrite: wrote=", wrote, " count=", cnt, " sum=", sum, " want=", want)
  in exit_void(1) end
end
