#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R
#use str as S

(* buf_writer_close_checked answers the final flush (#61): a writer on a
   read-only descriptor takes its byte into the buffer, and the flush at
   close fails with BadDescriptor. buf_writer_close, the published form
   kept beside it, still returns what it did: Ok, the flush dropped.
   Open flags are by the types (WriteOnly, ReadOnly). *)

fn check (name: string, got: string, want: string): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

fn is_bad (e: $F.io_error): bool =
  ($F.io_error_text(e) = $F.io_error_text($F.BadDescriptor()))

fn outcome_text (o: $F.close_outcome): string =
  case+ o of
  | ~$F.Closed() => "closed"
  | ~$F.FlushFailed(e) => (if is_bad(e) then "flush failed: bad descriptor" else "flush failed: other")
  | ~$F.CloseFailed(_) => "close failed"
  | ~$F.FlushAndCloseFailed(_, _) => "flush and close failed"

fn old_text (r: $R.result(int, $F.io_error)): string =
  case+ r of
  | ~$R.ok(_) => "ok"
  | ~$R.err(e) => $F.io_error_text(e)

(* A writer on p opened with access; pending bytes: 1 or 0 *)
fn open_writer {lp:agz}{np:pos | np < 1048576}
  (p: !$A.borrow(byte, lp, np), np: int np, access: $F.access, pending: int): $F.buf_writer =
  case+ $F.file_open(p, np, access, $F.CreateOrOpen(), 420) of
  | ~$R.ok(fd) => let
      val w = $F.buf_writer_create(fd)
      val () = (if pending > 0 then $R.discard<int><$F.io_error>($F.buf_write_byte(w, 97)) else ())
    in w end
  | ~$R.err(_) => let
      val () = println! ("FAIL open")
    in exit(1) end

implement main0 () = let
  var p = @[char][24]('/', 't', 'm', 'p', '/', 'b', 'a', 't', 's', '_', 'f', 'i', 'l', 'e', '_', 'c', 'l', 'o', 's', 'e', '.', 't', '\000', '\000')
  val @(fp, bp) = $A.freeze<byte>($S.from_char_array(p, 24))
  (* healthy writer *)
  val r1 = check("healthy, checked", outcome_text($F.buf_writer_close_checked(open_writer(bp, 24, $F.WriteOnly(), 1))), "closed")
  val r2 = check("healthy, old", old_text($F.buf_writer_close(open_writer(bp, 24, $F.WriteOnly(), 1))), "ok")
  (* the final write fails: read-only descriptor *)
  val r3 = check("failed final write, checked", outcome_text($F.buf_writer_close_checked(open_writer(bp, 24, $F.ReadOnly(), 1))), "flush failed: bad descriptor")
  val r4 = check("failed final write, old form still returns Ok", old_text($F.buf_writer_close(open_writer(bp, 24, $F.ReadOnly(), 1))), "ok")
  (* nothing pending: no write, no failure *)
  val r5 = check("nothing pending, checked", outcome_text($F.buf_writer_close_checked(open_writer(bp, 24, $F.ReadOnly(), 0))), "closed")
  val () = $A.drop<byte>(fp, bp)
  val () = $A.free<byte>($A.thaw<byte>(fp))
in
  if r1 && r2 && r3 && r4 && r5 then println! ("closeflush: all cases pass")
  else exit_void(1)
end
