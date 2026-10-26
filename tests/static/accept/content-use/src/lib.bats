#use array as A
#use file as F
#use result as R

(* A writer made, a byte written, closed with the proof of the one byte
   written; a reader opened, read once, and ended with the proof (keyword: content-io) *)
fn written_one (cw: $F.content_writer($A.cnil())): int =
  case+ $F.content_write_byte(cw, 65) of
  | ~$F.content_wrote(_ | cw2) =>
    (case+ $F.content_close(cw2) of
     | ~$F.content_closed(_ | _) => 0
     | ~$F.content_close_failed(_) => 1)
  | ~$F.content_write_failed(_) => 2

fn read_once {l:agz}{n:pos} (cr: $F.content_reader($A.cnil(), 0, 10), b: $A.barr(l, n, $A.cnil()), len: int n): int =
  case+ $F.content_read(cr, b, len) of
  | ~$F.content_read_some(_, _, _ | cr2, b2, _) => let
      val () = $F.content_reader_close(cr2)
      val () = $A.barr_free(b2)
    in 0 end
  | ~$F.content_read_limit(_, _ | b2) => let val () = $A.barr_free(b2) in 1 end
  | ~$F.content_read_eof(_ | b2) => let val () = $A.barr_free(b2) in 2 end
  | ~$F.content_read_failed(_, b2) => let val () = $A.barr_free(b2) in 3 end
