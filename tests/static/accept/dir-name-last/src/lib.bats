#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* The last byte of the next entry's name, read at index k - 1. dir_next's
   length is at most the buffer size, so index k - 1 is in bounds with no
   cast, and index k may not be. *)
#pub fn last_name_byte (d: !$F.dir): int

implement last_name_byte (d) = let
  val buf = $A.alloc<byte>(256)
  val k = (case+ $F.dir_next(d, buf, 256) of
    | ~$R.some(k) => k
    | ~$R.none() => 0): [k:nat | k <= 256] int k
  val j = (if k > 0 then k - 1 else 0): [j:nat | j < 256] int j
  val b = byte2int0($A.get<byte>(buf, j))
  val r = (if k > 0 then b else ~1): int
  val () = $A.free<byte>(buf)
in r end
