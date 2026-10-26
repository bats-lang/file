#use array as A
#use file as F

(* the writer after a byte is written, claimed to index what it did before *)
fn write_one {w:$A.cells} (cw: $F.content_writer(w)): void =
  case+ $F.content_write_byte(cw, 65) of
  | ~$F.content_wrote(_ | cw2) => let
      val cw3: $F.content_writer(w) = cw2
    in
      case+ $F.content_close(cw3) of
      | ~$F.content_closed(_ | _) => ()
      | ~$F.content_close_failed(_) => ()
    end
  | ~$F.content_write_failed(_) => ()
