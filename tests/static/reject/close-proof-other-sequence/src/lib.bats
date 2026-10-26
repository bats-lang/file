#use array as A
#use file as F

prfn needs_one_more {w:$A.cells} (h: $F.FILE_HOLDS($A.ccons(1, w))): void = ()

(* the proof of the cells written, used for the cells written and one more *)
fn close_one {w:$A.cells} (cw: $F.content_writer(w)): void =
  case+ $F.content_close(cw) of
  | ~$F.content_closed(holds | _) => let prval () = needs_one_more(holds) in () end
  | ~$F.content_close_failed(_) => ()
