#include "share/atspre_staload.hats"
#use arith as AR
#use array as A
#use file as F
#use result as R
#use str as S

(* The content writer and reader (keyword: content-io): what they write and
   read is the bytes of the test pattern; a stream copy through the reader and
   the writer ends with the three proofs side by side (the reader's end, the
   writer's close, and the equality of their cells, made by append_functional
   from each step's APPEND); failures are real ones (a directory read, a
   missing file, a write the kernel refuses). *)

fn check (name: string, ok: bool): bool = let
  val () = (if ok then () else println! ("FAIL ", name))
in ok end

(* The byte at position i of the test pattern *)
fn pat (i: int): [v:nat | v < 256] int v = $AR.low_byte(i * 7 + i / 256 + 3)

(* ---- a buffer holding the pattern from position base ---- *)

fun fill {l:agz}{n,i:nat | i <= n}{cs:$A.cells} .<n - i>.
  (a: $A.barr(l, n, cs), i: int i, n: int n, base: int): [cs2:$A.cells] $A.barr(l, n, cs2) =
  if i >= n then a
  else let
    val (_ | a2) = $A.barr_set(a, i, pat(base + i))
  in fill(a2, i + 1, n, base) end

(* bytes i up to k of the buffer are the pattern from position base + i *)
fun bytes_are {l:agz}{n:pos}{k,i:nat | k <= n; i <= k}{cs:$A.cells} .<k - i>.
  (a: !$A.barr(l, n, cs), i: int i, k: int k, base: int): bool =
  if i >= k then true
  else let
    val (_ | v) = $A.barr_get(a, i)
  in
    if v = pat(base + i) then bytes_are(a, i + 1, k, base) else false
  end

(* ---- a writer whose index is forgotten, to loop over it ---- *)

datavtype any_writer =
  | {w:$A.cells} any_writer_mk of $F.content_writer(w)

fun write_pattern {i,n:nat | i <= n} .<n - i>.
  (aw: any_writer, i: int i, n: int n): $R.result(any_writer, $F.io_error) =
  if i >= n then $R.ok(aw)
  else let
    val ~any_writer_mk(cw) = aw
  in
    case+ $F.content_write_byte(cw, pat(i)) of
    | ~$F.content_wrote(_ | cw2) => write_pattern(any_writer_mk(cw2), i + 1, n)
    | ~$F.content_write_failed(e) => $R.err(e)
  end

(* The pattern from base, m bytes, as one run *)
fn write_run {m:pos | m <= 1048576} (aw: any_writer, m: int m, base: int)
  : $R.result(any_writer, $F.io_error) = let
  val ~any_writer_mk(cw) = aw
  val (_ | a0) = $A.barr_alloc(m)
  val a = fill(a0, 0, m, base)
  val @(fz, b) = $A.barr_freeze(a)
  val r = $F.content_write(cw, fz, b, m)
  val () = $A.cborrow_drop(fz, b)
  val () = $A.barr_free($A.barr_thaw(fz))
in
  case+ r of
  | ~$F.content_wrote(_ | cw2) => $R.ok(any_writer_mk(cw2))
  | ~$F.content_write_failed(e) => $R.err(e)
end

fn flush_it (aw: any_writer): $R.result(any_writer, $F.io_error) = let
  val ~any_writer_mk(cw) = aw
in
  case+ $F.content_flush(cw) of
  | ~$F.content_flushed(cw2) => $R.ok(any_writer_mk(cw2))
  | ~$F.content_flush_failed(e) => $R.err(e)
end

(* closed: the proof made, or why not *)
fn close_it (aw: any_writer): $R.result(int, $F.io_error) = let
  val ~any_writer_mk(cw) = aw
in
  case+ $F.content_close(cw) of
  | ~$F.content_closed(_ | _) => $R.ok(0)
  | ~$F.content_close_failed(e) => $R.err(e)
end

fn is_error (e: $F.io_error, want: $F.io_error): bool =
  ($F.io_error_text(e) = $F.io_error_text(want))

(* ---- the file read back with the plain call: its first m bytes are the pattern ---- *)

fun arr_is_pattern {l:agz}{n:pos}{k,i:nat | k <= n; i <= k} .<k - i>.
  (a: !$A.arr(byte, l, n), i: int i, k: int k): bool =
  if i >= k then true
  else if byte2int0($A.get<byte>(a, i)) = pat(i) then arr_is_pattern(a, i + 1, k)
  else false

fn read_is_pattern {l:agz} (f: !$F.fd, a: !$A.arr(byte, l, 8192), m: int): bool =
  case+ $F.file_read(f, a, 8192) of
  | ~$R.err(_) => false
  | ~$R.ok(got) => (if got = m then arr_is_pattern(a, 0, got) else false)

fn file_is_pattern {lp:agz}{np:pos | np < 1048576} (p: !$A.borrow(byte, lp, np), np: int np, m: int): bool =
  case+ $F.file_open(p, np, $F.ReadOnly(), $F.OpenExisting(), 0) of
  | ~$R.err(_) => false
  | ~$R.ok(f) => let
      val a = $A.alloc<byte>(8192)
      val ok = read_is_pattern(f, a, m)
      val () = $A.free<byte>(a)
      val () = $R.discard<int><$F.io_error>($F.file_close(f))
    in ok end

(* ---- the reader to its end, chunk by chunk ---- *)

(* The bytes seen, and how it ended: 1 the limit, 2 the end of the file, 3 a
   failure that is want, 4 another failure, 0 a byte that is not the pattern
   (checked from position base + seen) or the fuel spent *)
fun read_all {consumed,buf:$A.cells}{start,limit:nat}{l:agz}{fuel:nat} .<fuel>.
  (cr: $F.content_reader(consumed, start, limit), buf: $A.barr(l, 64, buf),
   seen: int, base: int, fuel: int fuel, want: $F.io_error): @(int, int) =
  if fuel <= 0 then let
    val () = $F.content_reader_close(cr)
    val () = $A.barr_free(buf)
  in @(seen, 0) end
  else (case+ $F.content_read(cr, buf, 64) of
    | ~$F.content_read_some(_, _, _ | cr2, buf2, k) =>
        if bytes_are(buf2, 0, k, base + seen) then read_all(cr2, buf2, seen + k, base, fuel - 1, want)
        else let
          val () = $F.content_reader_close(cr2)
          val () = $A.barr_free(buf2)
        in @(seen, 0) end
    | ~$F.content_read_limit(_, _ | buf2) => let
        val () = $A.barr_free(buf2)
      in @(seen, 1) end
    | ~$F.content_read_eof(_ | buf2) => let
        val () = $A.barr_free(buf2)
      in @(seen, 2) end
    | ~$F.content_read_failed(e, buf2) => let
        val () = $A.barr_free(buf2)
      in @(seen, (if is_error(e, want) then 3 else 4)) end)

fn read_range {lp:agz}{np:pos | np < 1048576}{start,limit:nat}
  (p: !$A.borrow(byte, lp, np), np: int np, start: int start, limit: int limit, want: $F.io_error): @(int, int) =
  case+ $F.content_reader_open_range(p, np, start, limit) of
  | ~$R.err(_) => @(0, 5)
  | ~$R.ok(cr) => let
      val (_ | b) = $A.barr_alloc(64)
    in read_all(cr, b, 0, start, 100000, want) end

fn read_whole {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np): @(int, int) =
  case+ $F.content_reader_open(p, np) of
  | ~$R.err(_) => @(0, 5)
  | ~$R.ok(cr) => let
      val (_ | b) = $A.barr_alloc(64)
    in read_all(cr, b, 0, 0, 100000, $F.Unrecognized()) end

(* ---- a copy whose proofs meet: B holds exactly the cells read from A ---- *)

prfn same_after {consumed,written,chunk,more,both:$A.cells}
  (eq: $A.CELLS_EQ(consumed, written), p: $A.APPEND(consumed, chunk, more), q: $A.APPEND(written, chunk, both))
  : $A.CELLS_EQ(more, both) =
  case+ eq of $A.CELLS_EQ_refl() => $A.append_functional(p, q)

prfn holds_what_was_read {consumed,written:$A.cells}
  (eq: $A.CELLS_EQ(consumed, written), h: $F.FILE_HOLDS(written)): $F.FILE_HOLDS(consumed) =
  case+ eq of $A.CELLS_EQ_refl() => h

fn close_writer {written:$A.cells} (cw: $F.content_writer(written)): int =
  case+ $F.content_close(cw) of
  | ~$F.content_closed(_ | _) => 0
  | ~$F.content_close_failed(_) => 1

(* 0 when the reader ended and the writer closed, with FILE_HOLDS of the very
   cells FILE_READ names *)
fun copy_stream {consumed,written:$A.cells}{start,limit:nat}{l:agz}{buf:$A.cells}{fuel:nat} .<fuel>.
  (eq: $A.CELLS_EQ(consumed, written) |
   cr: $F.content_reader(consumed, start, limit), cw: $F.content_writer(written),
   buf: $A.barr(l, 64, buf), fuel: int fuel): int =
  if fuel <= 0 then let
    val () = $F.content_reader_close(cr)
    val () = $A.barr_free(buf)
    val _ = close_writer(cw)
  in 1 end
  else (case+ $F.content_read(cr, buf, 64) of
    | ~$F.content_read_some(size, holds, appended | cr2, buf2, k) => let
        val @(fz, b) = $A.barr_freeze(buf2)
        val r = $F.content_write_prefix(holds, size | cw, fz, b, k)
        val () = $A.cborrow_drop(fz, b)
        val buf3 = $A.barr_thaw(fz)
      in
        case+ r of
        | ~$F.content_wrote(appended2 | cw2) =>
            copy_stream(same_after(eq, appended, appended2) | cr2, cw2, buf3, fuel - 1)
        | ~$F.content_write_failed(_) => let
            val () = $F.content_reader_close(cr2)
            val () = $A.barr_free(buf3)
          in 1 end
      end
    | ~$F.content_read_limit(ended, _ | buf2) => let
        val () = $A.barr_free(buf2)
      in
        case+ $F.content_close(cw) of
        | ~$F.content_closed(holds | _) => let
            prval _ = (ended, holds_what_was_read(eq, holds))
          in 0 end
        | ~$F.content_close_failed(_) => 1
      end
    | ~$F.content_read_eof(ended | buf2) => let
        val () = $A.barr_free(buf2)
      in
        case+ $F.content_close(cw) of
        | ~$F.content_closed(holds | _) => let
            prval _ = (ended, holds_what_was_read(eq, holds))
          in 0 end
        | ~$F.content_close_failed(_) => 1
      end
    | ~$F.content_read_failed(_, buf2) => let
        val () = $A.barr_free(buf2)
        val _ = close_writer(cw)
      in 1 end)

fn copy_file {la:agz}{na:pos | na < 1048576}{lb:agz}{nb:pos | nb < 1048576}
  (pa: !$A.borrow(byte, la, na), na: int na, pb: !$A.borrow(byte, lb, nb), nb: int nb): int =
  case+ $F.content_reader_open(pa, na) of
  | ~$R.err(_) => 1
  | ~$R.ok(cr) =>
    (case+ $F.content_create(pb, nb, 420) of
     | ~$R.err(_) => let val () = $F.content_reader_close(cr) in 1 end
     | ~$R.ok(cw) => let
         val (_ | buf) = $A.barr_alloc(64)
       in copy_stream($A.CELLS_EQ_refl() | cr, cw, buf, 100000) end)

(* ---- the writer ---- *)

(* The test file: single bytes, a run that is buffered, a flush, and a run
   larger than the buffer; how it ended: 0 closed with the proof *)
fn write_test_file {lp:agz}{np:pos | np < 1048576} (p: !$A.borrow(byte, lp, np), np: int np): int =
  case+ $F.content_create(p, np, 420) of
  | ~$R.err(_) => 1
  | ~$R.ok(cw) =>
    (case+ write_pattern(any_writer_mk(cw), 0, 300) of
     | ~$R.err(_) => 2
     | ~$R.ok(a1) =>
       (case+ write_run(a1, 200, 300) of
        | ~$R.err(_) => 3
        | ~$R.ok(a2) =>
          (case+ flush_it(a2) of
           | ~$R.err(_) => 4
           | ~$R.ok(a3) =>
             (case+ write_run(a3, 4000, 500) of
              | ~$R.err(_) => 5
              | ~$R.ok(a4) =>
                (case+ close_it(a4) of
                 | ~$R.err(_) => 6
                 | ~$R.ok(_) => 0)))))

(* A write the kernel refuses (a byte that is not a number, to a file of the
   process's own that takes only numbers): how each call answered *)
fn refused_byte {lp:agz}{np:pos | np < 1048576} (p: !$A.borrow(byte, lp, np), np: int np): bool =
  case+ $F.content_create(p, np, 420) of
  | ~$R.err(_) => false
  | ~$R.ok(cw) =>
    (case+ write_pattern(any_writer_mk(cw), 0, 1) of
     | ~$R.err(_) => false
     | ~$R.ok(a1) =>
       (case+ close_it(a1) of
        | ~$R.err(e) => is_error(e, $F.InvalidInput())
        | ~$R.ok(_) => false))

fn refused_run {lp:agz}{np:pos | np < 1048576} (p: !$A.borrow(byte, lp, np), np: int np): bool =
  case+ $F.content_create(p, np, 420) of
  | ~$R.err(_) => false
  | ~$R.ok(cw) =>
    (case+ write_run(any_writer_mk(cw), 5000, 0) of
     | ~$R.err(e) => is_error(e, $F.InvalidInput())
     | ~$R.ok(a1) => let val () = $R.discard<int><$F.io_error>(close_it(a1)) in false end)

(* one read, then closed before the end *)
fn early_close {lp:agz}{np:pos | np < 1048576} (p: !$A.borrow(byte, lp, np), np: int np): bool =
  case+ $F.content_reader_open(p, np) of
  | ~$R.err(_) => false
  | ~$R.ok(cr) => let
      val (_ | b) = $A.barr_alloc(64)
    in
      case+ $F.content_read(cr, b, 64) of
      | ~$F.content_read_some(_, _, _ | cr2, b2, k) => let
          val () = $F.content_reader_close(cr2)
          val () = $A.barr_free(b2)
        in k = 64 end
      | ~$F.content_read_limit(_, _ | b2) => let val () = $A.barr_free(b2) in false end
      | ~$F.content_read_eof(_ | b2) => let val () = $A.barr_free(b2) in false end
      | ~$F.content_read_failed(_, b2) => let val () = $A.barr_free(b2) in false end
    end

implement main0 () = let
  var pa = @[char][14]('/', 't', 'm', 'p', '/', 'f', '7', '6', '_', 'a', '.', 'b', 'i', 'n')
  var pb = @[char][14]('/', 't', 'm', 'p', '/', 'f', '7', '6', '_', 'b', '.', 'b', 'i', 'n')
  var pd = @[char][4]('/', 't', 'm', 'p')
  var pm = @[char][16]('/', 't', 'm', 'p', '/', 'f', '7', '6', '_', 'm', 'i', 's', 's', 'i', 'n', 'g')
  var pz = @[char][24]('/', 'p', 'r', 'o', 'c', '/', 's', 'e', 'l', 'f', '/', 'o', 'o', 'm', '_', 's', 'c', 'o', 'r', 'e', '_', 'a', 'd', 'j')
  val @(fa, ba) = $A.freeze<byte>($S.from_char_array(pa, 14))
  val @(fb, bb) = $A.freeze<byte>($S.from_char_array(pb, 14))
  val @(fd, bd) = $A.freeze<byte>($S.from_char_array(pd, 4))
  val @(fm, bm) = $A.freeze<byte>($S.from_char_array(pm, 16))
  val @(fz, bz) = $A.freeze<byte>($S.from_char_array(pz, 24))
  (* writing *)
  val w1 = check("write the test file", write_test_file(ba, 14) = 0)
  val w2 = check("the file holds the pattern", file_is_pattern(ba, 14, 4500))
  (* reading it back *)
  val @(n3, c3) = read_whole(ba, 14)
  val r1 = check("whole file: all bytes, end of file", n3 = 4500 && c3 = 2)
  val @(n4, c4) = read_range(ba, 14, 100, 50, $F.Unrecognized())
  val r2 = check("range inside: the limit", n4 = 50 && c4 = 1)
  val @(n5, c5) = read_range(ba, 14, 4490, 50, $F.Unrecognized())
  val r3 = check("range past the end: end of file after the rest", n5 = 10 && c5 = 2)
  val @(n6, c6) = read_range(ba, 14, 4600, 20, $F.Unrecognized())
  val r4 = check("range after the end: end of file at once", n6 = 0 && c6 = 2)
  val @(n7, c7) = read_range(ba, 14, 7, 0, $F.Unrecognized())
  val r5 = check("limit of nothing: the limit at once", n7 = 0 && c7 = 1)
  val @(n8, c8) = read_range(bd, 4, 0, 10, $F.IsADirectory())
  val r6 = check("a directory: the read fails", n8 = 0 && c8 = 3)
  val @(n9, c9) = read_range(bm, 16, 0, 10, $F.Unrecognized())
  val r7 = check("a missing file: no reader", n9 = 0 && c9 = 5)
  val r8 = check("closed before the end", early_close(ba, 14))
  (* the copy: B holds what was read *)
  val k1 = check("stream copy", copy_file(ba, 14, bb, 14) = 0)
  val k2 = check("the copy holds the pattern", file_is_pattern(bb, 14, 4500))
  (* the kernel refuses a write *)
  val f1 = check("a refused byte fails the close", refused_byte(bz, 24))
  val f2 = check("a refused run fails the write", refused_run(bz, 24))
  val () = $A.drop<byte>(fa, ba)
  val () = $A.free<byte>($A.thaw<byte>(fa))
  val () = $A.drop<byte>(fb, bb)
  val () = $A.free<byte>($A.thaw<byte>(fb))
  val () = $A.drop<byte>(fd, bd)
  val () = $A.free<byte>($A.thaw<byte>(fd))
  val () = $A.drop<byte>(fm, bm)
  val () = $A.free<byte>($A.thaw<byte>(fm))
  val () = $A.drop<byte>(fz, bz)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in
  if w1 && w2 && r1 && r2 && r3 && r4 && r5 && r6 && r7 && r8 && k1 && k2 && f1 && f2
  then println! ("contentio: all cases pass")
  else exit_void(1)
end
