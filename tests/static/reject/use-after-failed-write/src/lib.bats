#use array as A
#use file as F

(* the writer a failed write consumed, closed again *)
fn write_then_close {w:$A.cells} (cw: $F.content_writer(w)): void =
  case+ $F.content_write_byte(cw, 65) of
  | ~$F.content_wrote(_ | cw2) => (case+ $F.content_close(cw2) of
      | ~$F.content_closed(_ | _) => ()
      | ~$F.content_close_failed(_) => ())
  | ~$F.content_write_failed(_) =>
    (case+ $F.content_close(cw) of
      | ~$F.content_closed(_ | _) => ()
      | ~$F.content_close_failed(_) => ())
