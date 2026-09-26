#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* The last byte of entry 0's name, read at index k - 1. entries_name's
   length is at most the buffer size, so index k - 1 is in bounds with no
   cast, and index k may not be. *)
#pub fn last_name_byte {n:pos} (es: !$F.entries(n)): int

implement last_name_byte {n} (es) = let
  val buf = $A.alloc<byte>(256)
  val k = $F.entries_name(es, 0, buf, 256)
  val j = (if k > 0 then k - 1 else 0): [j:nat | j < 256] int j
  val b = byte2int0($A.get<byte>(buf, j))
  val r = (if k > 0 then b else ~1): int
  val () = $A.free<byte>(buf)
in r end
