#use array as A
#use file as F

prfn needs_start_one {c:$A.cells}{lim:nat} (r: $F.FILE_READ(c, 1, lim)): void = ()

(* the proof of the range from the first byte, used for the range from the second *)
fn read_end {c,b:$A.cells}{lim:nat}{l:agz}{n:pos}
  (cr: $F.content_reader(c, 0, lim), buf: $A.barr(l, n, b), len: int n): void =
  case+ $F.content_read(cr, buf, len) of
  | ~$F.content_read_some(_, _, _ | cr2, b2, _) => let
      val () = $F.content_reader_close(cr2)
    in $A.barr_free(b2) end
  | ~$F.content_read_limit(ended, _ | b2) => let prval () = needs_start_one(ended) in $A.barr_free(b2) end
  | ~$F.content_read_eof(_ | b2) => $A.barr_free(b2)
  | ~$F.content_read_failed(_, b2) => $A.barr_free(b2)
