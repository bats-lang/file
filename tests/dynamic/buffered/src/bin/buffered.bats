#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* Writes "ab\ncd\nxyz" through buf_writer (bytes and a block), reads it
   back with buf_read_line and buf_read. Exits 1 on any mismatch.
   Open flags are Linux values (577 = O_WRONLY|O_CREAT|O_TRUNC), as in
   the rest of bats-lang for now. *)
fn check (name: string, ok: bool): bool = let
  val () = (if ok then () else println! ("FAIL ", name))
in ok end

fn line_is {l:agz}{m:pos}{k:nat | k <= m; k <= 1048576} (buf: !$A.arr(byte, l, m), r: $R.option(int), want: &(@[char][k]), k: int k): bool =
  case+ r of
  | ~$R.some(n) =>
      if n != k then false
      else if k = 0 then true
      else let
        val @(fw, bw) = $A.freeze<byte>($S.from_char_array(want, k))
        val ok = $S.match_at_arr(buf, 0, bw, k)
        val () = $A.drop<byte>(fw, bw)
        val () = $A.free<byte>($A.thaw<byte>(fw))
      in ok end
  | ~$R.none() => false

implement main0 () = let
  var p = @[char][24]('/', 't', 'm', 'p', '/', 'b', 'a', 't', 's', '_', 'f', 'i', 'l', 'e', '_', 't', 'e', 's', 't', '.', 't', 'x', 't', '\000')
  val @(fp, bp) = $A.freeze<byte>($S.from_char_array(p, 24))
  (* write *)
  val w_ok = (case+ $F.file_open(bp, 24, $F.WriteOnly(), $F.CreateOrTruncate(), 420) of
    | ~$R.ok(fd) => let
        val w = $F.buf_writer_create(fd)
        val () = $R.discard<int><$F.io_error>($F.buf_write_byte(w, 97))
        val () = $R.discard<int><$F.io_error>($F.buf_write_byte(w, 98 + 256)   (* low byte: 'b' *))
        val () = $R.discard<int><$F.io_error>($F.buf_write_byte(w, 10))
        var blk = @[char][6]('c', 'd', '\n', 'x', 'y', 'z')
        val @(fb, bb) = $A.freeze<byte>($S.from_char_array(blk, 6))
        val () = $R.discard<int><$F.io_error>($F.buf_write(w, bb, 6))
        val () = $A.drop<byte>(fb, bb)
        val () = $A.free<byte>($A.thaw<byte>(fb))
        val c = $F.buf_writer_close(w)
        val () = $R.discard<int><$F.io_error>(c)
      in true end
    | ~$R.err(_) => false): bool
  val r0 = check("open for write", w_ok)
  (* read back *)
  val r_ok = (case+ $F.file_open(bp, 24, $F.ReadOnly(), $F.OpenExisting(), 0) of
    | ~$R.ok(fd) => let
        val r = $F.buf_reader_create(fd)
        val buf = $A.alloc<byte>(8)
        var ab = @[char][2]('a', 'b')
        var cd = @[char][2]('c', 'd')
        var xyz = @[char][3]('x', 'y', 'z')
        val a1 = check("line 1", line_is(buf, $F.buf_read_line(r, buf, 8), ab, 2))
        val a2 = check("line 2", line_is(buf, $F.buf_read_line(r, buf, 8), cd, 2))
        val a3 = check("last line, no newline", line_is(buf, $F.buf_read_line(r, buf, 8), xyz, 3))
        val a4 = check("end of file", (case+ $F.buf_read_line(r, buf, 8) of
          | ~$R.some(_) => false | ~$R.none() => true))
        val () = $A.free<byte>(buf)
        val c = $F.buf_reader_close(r)
        val () = $R.discard<int><$F.io_error>(c)
      in a1 && a2 && a3 && a4 end
    | ~$R.err(_) => check("open for read", false)): bool
  (* buf_read in two chunks *)
  val c_ok = (case+ $F.file_open(bp, 24, $F.ReadOnly(), $F.OpenExisting(), 0) of
    | ~$R.ok(fd) => let
        val r = $F.buf_reader_create(fd)
        val buf = $A.alloc<byte>(4)
        var abnc = @[char][4]('a', 'b', '\n', 'c')
        var dnxy = @[char][4]('d', '\n', 'x', 'y')
        val b1 = check("read 4", line_is(buf, $F.buf_read(r, buf, 4), abnc, 4))
        val b2 = check("read next 4", line_is(buf, $F.buf_read(r, buf, 4), dnxy, 4))
        val () = $A.free<byte>(buf)
        val c = $F.buf_reader_close(r)
        val () = $R.discard<int><$F.io_error>(c)
      in b1 && b2 end
    | ~$R.err(_) => check("open for chunked read", false)): bool
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
in
  if r0 && r_ok && c_ok then println! ("buffered: all cases pass")
  else exit_void(1)
end
