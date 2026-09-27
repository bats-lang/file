#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* A 256-byte buffer is too small for entries_name: a name can have up
   to ENTRY_NAME_MAX bytes (1024, on macOS), and entries_name copies it
   whole rather than truncating it. *)
#pub fn name_len {n:pos} (es: !$F.entries(n)): int

implement name_len {n} (es) = let
  val buf = $A.alloc<byte>(256)
  val k = $F.entries_name(es, 0, buf, 256)
  val () = $A.free<byte>(buf)
in k end
