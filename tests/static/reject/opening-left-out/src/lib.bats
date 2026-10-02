#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A match on an opening that leaves appending to an existing file out *)
fn creates (opening: $F.opening): bool =
  case+ opening of
  | $F.OpenExisting() => false
  | $F.CreateOrOpen() => true
  | $F.CreateOrTruncate() => true
  | $F.CreateOrAppend() => true
  | $F.TruncateExisting() => false
