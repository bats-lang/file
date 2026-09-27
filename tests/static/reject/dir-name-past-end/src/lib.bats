#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* The last byte of entry 0's name, read at index k. entries_name's name
   is shorter than the buffer, so index k - 1 is in bounds with no
   cast, and index k may not be. *)
#pub fn last_name_byte {n:pos} (es: !$F.entries(n)): int

implement last_name_byte {n} (es) = let
  val buf = $A.alloc<byte>(1024)
  val k = $F.entries_name(es, 0, buf, 1024)
  val j = (if k > 0 then k else 0): [j:nat | j < 1024] int j
  val b = byte2int0($A.get<byte>(buf, j))
  val r = (if k > 0 then b else ~1): int
  val () = $A.free<byte>(buf)
in r end
