#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A match on why an operation failed that names only some kinds *)
fn missing (e: $F.io_error): bool =
  case+ e of
  | $F.NotFound() => true
  | $F.NotADirectory() => true
