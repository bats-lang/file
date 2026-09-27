#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* file_read fills an arena's piece as it does an alloc'd array: a file
   larger than alloc's bound is read into one piece *)
#pub fn read_big (f: !$F.fd): int

implement read_big (f) =
  case+ $A.arena_create<byte>(2097152) of
  | ~$A.arena_none() => ~1
  | ~$A.arena_some(ar) => let
      val p = $A.arena_alloc<byte>(ar, 2097152)
      val r = $F.file_read(f, p, 2097152)
      val n = (case+ r of | ~$R.ok(k) => k | ~$R.err(_) => ~1): int
      val () = $A.arena_return<byte>(ar, p)
      val () = $A.arena_destroy<byte>(ar)
    in n end
