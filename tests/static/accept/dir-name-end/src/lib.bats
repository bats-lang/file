#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* The byte after entry 0's name, read at index k. entries_name's name
   is shorter than ENTRY_NAME_MAX (1024), so index k is in the 1024-byte
   buffer with no cast, and index k + 1 may not be. *)
#pub fn after_name_byte {n:pos} (es: !$F.entries(n)): int

implement after_name_byte {n} (es) = let
  val buf = $A.alloc<byte>(1024)
  val k = $F.entries_name(es, 0, buf, 1024)
  val b = byte2int0($A.get<byte>(buf, k))
  val () = $A.free<byte>(buf)
in b end
