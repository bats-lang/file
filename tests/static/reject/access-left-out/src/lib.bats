#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A match on an access that leaves read-write out *)
fn writes (access: $F.access): bool =
  case+ access of
  | $F.ReadOnly() => false
  | $F.WriteOnly() => true
