#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A close_outcome match that leaves out the flush's failure, as the old
   close did (#61): not every case is handled, so it is rejected *)
fn missing (o: $F.close_outcome): bool =
  case+ o of
  | ~$F.Closed() => true
  | ~$F.CloseFailed(_) => false
  | ~$F.FlushAndCloseFailed(_, _) => false
