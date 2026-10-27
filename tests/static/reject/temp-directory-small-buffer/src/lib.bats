#include "share/atspre_staload.hats"
#use array as A
#use file as F
#use result as R

(* The path of a temporary directory is the prefix and six more bytes: a
   buffer of 17 for a prefix of 12 is too small, and nothing truncates. *)
#pub fn make_in_small {lb:agz}
  (name_prefix: !$A.borrow(byte, lb, 12)): int

implement make_in_small (name_prefix) = let
  val out = $A.alloc<byte>(17)
  val r = (case+ $F.file_make_temp_directory(name_prefix, 12, out, 17) of
    | ~$F.TempDirectoryMade() => 0
    | ~$F.TempDirectoryFailed(_) => 1)
  val () = $A.free<byte>(out)
in r end
