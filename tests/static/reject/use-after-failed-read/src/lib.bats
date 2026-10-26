#use array as A
#use file as F

(* the reader a failed read consumed, closed again *)
fn read_then_close {c,b:$A.cells}{s,lim:nat}{l:agz}{n:pos}
  (cr: $F.content_reader(c, s, lim), buf: $A.barr(l, n, b), len: int n): void =
  case+ $F.content_read(cr, buf, len) of
  | ~$F.content_read_some(_, _, _ | cr2, b2, _) => let
      val () = $F.content_reader_close(cr2)
    in $A.barr_free(b2) end
  | ~$F.content_read_limit(_, _ | b2) => $A.barr_free(b2)
  | ~$F.content_read_eof(_ | b2) => $A.barr_free(b2)
  | ~$F.content_read_failed(_, b2) => let
      val () = $F.content_reader_close(cr)
    in $A.barr_free(b2) end
